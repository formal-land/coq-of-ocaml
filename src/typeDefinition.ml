open Typedtree
open SmartPrint
open Monad.Notations

let to_coq_record
  (generate_withs : bool)
  (module_name : Name.t)
  (typ_name : Name.t)
  (typ_args : Name.t list)
  (fields : (Name.t * Type.t) list)
  : SmartPrint.t =
  nest (
    !^ "Module" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
    indent (
      !^ "Record" ^^ !^ "record" ^^
      begin match typ_args with
      | [] -> empty
      | _ :: _ ->
        braces (nest (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ Pp.set
        ))
      end ^^
      !^ ":=" ^^
      begin if generate_withs then
        !^ "Build"
      else
        empty
      end ^^
      !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None typ)))) ^^
      !^ "}." ^^
      begin match typ_args with
      | [] -> empty
      | _ :: _ ->
        newline ^^ !^ "Arguments" ^^ !^ "record" ^^ !^ ":" ^^
        !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
      end ^^
      begin if generate_withs then
        newline ^^ separate newline (fields |> List.map (fun (name, _) ->
          let prefixed_typ_args =
            typ_args |> List.map (fun typ_arg ->
              Name.to_coq (Name.prefix_by_t typ_arg)
             ) in
          let record_typ =
            nest (separate space (!^ "record" :: prefixed_typ_args)) in
          nest (
            !^ "Definition" ^^ Name.to_coq (Name.prefix_by_with name) ^^
            begin match typ_args with
            | [] -> empty
            | _ :: _ -> braces (nest (separate space prefixed_typ_args))
            end ^^
            Name.to_coq name ^^
            nest (parens (!^ "r" ^^ !^ ":" ^^ record_typ)) ^-^
            !^ " :=" ^^ newline ^^
            indent @@ nest (
              !^ "Build" ^^
              separate space prefixed_typ_args ^^
              separate space (fields |> List.map (fun (name', _) ->
                nest (
                  if Name.equal name name' then
                    Name.to_coq name
                  else
                  !^ "r" ^-^ !^ ".(" ^-^ Name.to_coq name' ^-^ !^ ")"
                )
              )) ^-^ !^ "."
            )
          )
        ))
      else
        empty
      end
    ) ^^ newline ^^
    !^ "End" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
    nest (
      !^ "Definition" ^^ Name.to_coq typ_name ^^ !^ ":=" ^^
      Name.to_coq module_name ^-^ !^ ".record" ^-^ !^ "."
    )
  )

module RecordSkeleton = struct
  type t = {
    fields : Name.t list;
    module_name : Name.t;
    typ_name : Name.t;
  }

  let to_coq (generate_withs : bool) (record_skeleton : t) : SmartPrint.t =
    let { fields; module_name; typ_name } = record_skeleton in
    to_coq_record generate_withs module_name typ_name fields (fields |>
      List.map (fun field -> (field, Type.Variable field))
    )
end

module TypeVariable = struct
  type t =
    | Error
    | Known of Name.t
    | Unknown
end

let rec named_typ_param (typ : Types.type_expr) : TypeVariable.t =
  match typ.Types.desc with
  | Tvar x | Tunivar x ->
    begin match x with
    | None | Some "_" -> TypeVariable.Unknown
    | Some x -> TypeVariable.Known (Name.of_string false x)
    end
  | Tlink typ | Tsubst typ -> named_typ_param typ
  | _ -> TypeVariable.Error

let named_typ_params_expecting_anything (typs : Types.type_expr list)
  : Name.t option list option =
  typs |>
  List.map named_typ_param |>
  List.map (function
    | TypeVariable.Error -> None
    | Known name -> Some (Some name)
    | Unknown -> Some None
  ) |>
  Util.Option.all

let named_typ_params_expecting_variables (typs : Types.type_expr list)
  : Name.t option list Monad.t =
  typs |>
  List.map named_typ_param |>
  Monad.List.map (function
    | TypeVariable.Error ->
      raise
        (Some (Name.of_string false "expected_type_variable"))
        Unexpected
        "Expected a list of named or unspecified '_' type variables"
    | Known name -> return (Some name)
    | Unknown -> return None
  )

let named_typ_params_with_unknowns (typ_params : Name.t option list)
  : Name.t list =
  typ_params |> List.map (function
    | Some typ_param -> typ_param
    | None -> Name.of_string false "_"
  )

(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
module Constructors = struct
  (** [constructor_name]: forall [typ_vars], [param_typs] -> t [res_typ_params] *)
  type item = {
    constructor_name : Name.t;
    param_typs : Type.t list; (** The parameters of the constructor. *)
    res_typ_params : Type.t list; (** The type parameters of the result type of the constructor. *)
    typ_vars : Name.t list; (** The polymorphic type variables. *)
  }

  type t = item list

  module Single = struct
    type t = {
      constructor_name : Name.t;
      param_typs : Type.t list; (** The parameters of the constructor. *)
      return_typ_params : Name.t option list option;
        (** The return type, in case of GADT contructor *)
    }

    let of_ocaml_case
      (typ_name : Name.t)
      (defined_typ_params : Name.t option list)
      (case : Types.constructor_declaration)
      : (t * (RecordSkeleton.t * Name.t list * Type.t) option) Monad.t =
      let { Types.cd_args; cd_id; cd_loc; cd_res; _ } = case in
      set_loc (Loc.of_location cd_loc) (
      let constructor_name = Name.of_ident false cd_id in
      let typ_vars = Name.Map.empty in
      begin match cd_args with
      | Cstr_tuple param_typs ->
        Type.of_typs_exprs true typ_vars param_typs >>= fun (param_typs, _, _) ->
        return (param_typs, None)
      | Cstr_record labeled_typs ->
        set_loc (Loc.of_location cd_loc) (
        (
          labeled_typs |>
          List.map (fun { Types.ld_type; _ } -> ld_type) |>
          Type.of_typs_exprs true typ_vars
        ) >>= fun (record_params, _, _) ->
        let record_fields = labeled_typs |> List.map ( fun { Types.ld_id; _ } ->
          Name.of_ident false ld_id
        ) in
        let typ_args =
          Name.Set.elements (Type.typ_args_of_typs record_params) in
        return (
          [
            Type.Apply (
              MixedPath.PathName {
                path = [typ_name];
                base = constructor_name;
              },
              typ_args |> List.map (fun name ->
                Type.Variable name
              )
            )
          ],
          Some (
            {
              RecordSkeleton.fields = record_fields;
              module_name = constructor_name;
              typ_name = Name.suffix_by_skeleton constructor_name;
            },
            typ_args,
            Type.Apply (
              MixedPath.PathName {
                path = [typ_name];
                base = Name.suffix_by_skeleton constructor_name;
              },
              record_params
            )
          )
        ))
      end >>= fun (param_typs, records) ->
      let return_typ_params =
        match cd_res with
        | Some { Types.desc = Tconstr (_, typs, _); _ } ->
          named_typ_params_expecting_anything typs
        | Some _ -> None
        | None -> Some defined_typ_params in
      return (
        {
          constructor_name;
          param_typs;
          return_typ_params;
        },
        records
      ))

    let of_ocaml_row
      (defined_typ_params : Name.t option list)
      (row : Asttypes.label * Types.row_field)
      : t Monad.t =
      let (label, field) = row in
      let typs = Type.type_exprs_of_row_field field in
      Type.of_typs_exprs true Name.Map.empty typs >>= fun (param_typs, _, _) ->
      return {
        constructor_name = Name.of_string false label;
        param_typs;
        return_typ_params = Some defined_typ_params;
      }
  end

  let gadt_typ (typ_name : Name.t) : Type.t =
    Type.Apply (MixedPath.of_name (Name.suffix_by_gadt typ_name), [])

  let rec subst_gadt_typ_constructor (typ_name : Name.t) (typ : Type.t)
    : Type.t =
    match typ with
    | Variable _ -> typ
    | Arrow (typ_arg, typ_res) ->
      Arrow (
        subst_gadt_typ_constructor typ_name typ_arg,
        subst_gadt_typ_constructor typ_name typ_res
      )
    | Sum typs ->
      Sum (typs |> List.map (fun (name, typ) ->
        (name, subst_gadt_typ_constructor typ_name typ))
      )
    | Tuple typs -> Tuple (List.map (subst_gadt_typ_constructor typ_name) typs)
    | Apply (path, typs) ->
      begin match path with
      | PathName { path = []; base } when base = typ_name -> gadt_typ typ_name
      | _ -> Apply (path, List.map (subst_gadt_typ_constructor typ_name) typs)
      end
    | Package (path, tree) ->
      Package (path, tree |> Tree.map (fun typ ->
        match typ with
        | None -> typ
        | Some typ -> Some (subst_gadt_typ_constructor typ_name typ)
      ))
    | ForallModule (name, param, result) ->
      ForallModule (
        name,
        subst_gadt_typ_constructor typ_name param,
        if Name.equal typ_name name then
          result
        else
          subst_gadt_typ_constructor typ_name result
      )
    | ForallTyps (typ_args, typ) ->
      if Name.Set.mem typ_name (Name.Set.of_list typ_args) then
        typ
      else
        ForallTyps (typ_args, subst_gadt_typ_constructor typ_name typ)
    | Error _ -> typ

  let rec merge_typ_params
    (params1 : Name.t option list)
    (params2 : Name.t option list)
    : Name.t option list option =
    match (params1, params2) with
    | ([], []) -> Some []
    | (_ :: _, []) | ([], _ :: _) -> None
    | (param1 :: params1, param2 :: params2) ->
      Util.Option.bind (merge_typ_params params1 params2) (fun params ->
      match (param1, param2) with
      | (Some param1, Some param2) ->
        if Name.equal param1 param2 then
          Some (Some param1 :: params)
        else
          None
      | (Some param, None) | (None, Some param) -> Some (Some param :: params)
      | (None, None) -> Some (None :: params))

  (** Check if the type is not a GADT. If this is not a GADT, also return a
      prefered list of parameter names for the type variables. It merges the
      names found in the definition of the type name and in the constructors. *)
  let rec check_if_not_gadt
    (defined_typ_params : Name.t option list)
    (single_constructors : Single.t list)
    : Name.t option list option =
    match single_constructors with
    | [] -> Some defined_typ_params
    | { Single.return_typ_params; _ } :: single_constructors ->
      begin match return_typ_params with
      | None -> None
      | Some return_typ_params ->
        let are_variables_different =
          let non_null_variables =
            Util.List.filter_map (fun x -> x) return_typ_params in
          List.length non_null_variables <>
            Name.Set.cardinal (Name.Set.of_list non_null_variables) in
        if are_variables_different then
          None
        else
          Util.Option.bind
            (merge_typ_params defined_typ_params return_typ_params)
            (fun defined_typ_params ->
              check_if_not_gadt defined_typ_params single_constructors
            )
      end

  let of_ocaml
    (typ_name : Name.t)
    (defined_typ_params : Name.t option list)
    (single_constructors : Single.t list)
    : (t * Name.t option list option) Monad.t =
    let merged_typ_params =
      check_if_not_gadt defined_typ_params single_constructors in
    let constructors = single_constructors |> List.map (
      fun { Single.constructor_name; param_typs; _ } ->
        match merged_typ_params with
        | None ->
          let param_typs =
            param_typs |> List.map (subst_gadt_typ_constructor typ_name) in
          {
            constructor_name;
            param_typs;
            res_typ_params = [];
            typ_vars = Name.Set.elements (Type.typ_args_of_typs param_typs)
          }
        | Some merged_typ_params ->
          {
            constructor_name;
            param_typs;
            res_typ_params =
              List.map (fun name -> Type.Variable name)
                (named_typ_params_with_unknowns merged_typ_params);
            typ_vars =
              Name.Set.elements (
                Name.Set.diff
                  (Type.typ_args_of_typs param_typs)
                  (merged_typ_params |>
                    Util.List.filter_map (fun x -> x) |>
                    Name.Set.of_list
                  )
              )
          }
    ) in
    return (constructors, merged_typ_params)
end

module Inductive = struct
  type t = {
    constructor_records
      : (Name.t * (RecordSkeleton.t * Name.t list * Type.t) list) list;
    notations : (Name.t * Name.t option list * Type.t) list;
    records : RecordSkeleton.t list;
    typs : (Name.t * Name.t option list * Constructors.t) list;
  }

  let to_coq_constructor_records (inductive : t) : SmartPrint.t list =
    inductive.constructor_records |> List.map (fun (name, records) ->
      !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
      indent (
        separate
          (newline ^^ newline)
          (records |> List.map (fun (record, _, _) ->
            RecordSkeleton.to_coq false record
          ))
      ) ^^ newline ^^
      !^ "End" ^^ Name.to_coq name ^-^ !^ "."
    )

  let to_coq_notation_name (name : Name.t) : SmartPrint.t =
    !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\""

  let to_coq_notation_record (prefix : Name.t) (name : Name.t) : SmartPrint.t =
    !^ "\"'" ^-^ Name.to_coq prefix ^-^ !^ "." ^-^ Name.to_coq name ^-^ !^ "\""

  let to_coq_notations_reserved (inductive : t) : SmartPrint.t list =
    (inductive.constructor_records |> List.map
      (fun (name, records) ->
        records |> List.map (fun ({ RecordSkeleton.module_name; _ }, _, _) ->
          !^ "Reserved Notation" ^^ to_coq_notation_record name module_name ^-^
          !^ "."
        )
      )
      |> List.concat
    ) @
    (inductive.notations |> List.map (fun (name, _, _) ->
      !^ "Reserved Notation" ^^ to_coq_notation_name name ^-^ !^ "."
    ))

  let to_coq_record_skeletons (inductive : t) : SmartPrint.t list =
    inductive.records |> List.map (RecordSkeleton.to_coq true)

  let to_coq_typs
    (subst : Type.Subst.t)
    (is_first : bool)
    (name : Name.t)
    (left_typ_args : Name.t option list)
    (constructors : Constructors.t)
    : SmartPrint.t =
    let keyword = if is_first then !^ "Inductive" else !^ "with" in
    nest (
      keyword ^^ Name.to_coq name ^^
      (if left_typ_args = [] then
        empty
      else
        parens (
          nest (
            separate space (left_typ_args |> List.map (function
              None -> !^ "_"
              | Some name -> Name.to_coq name
            )) ^^
            !^ ":" ^^ Pp.set
          )
        )
      ) ^^ !^ ":" ^^ Pp.set ^^ !^ ":=" ^-^
      separate empty (
        constructors |> List.map (fun { Constructors.constructor_name; param_typs; res_typ_params; typ_vars } ->
          newline ^^ nest (
            !^ "|" ^^ Name.to_coq constructor_name ^^ !^ ":" ^^
            (match typ_vars with
            | [] -> empty
            | _ ->
              !^ "forall" ^^ braces (
                separate space (typ_vars |> List.map Name.to_coq) ^^ !^ ":" ^^ Pp.set
              ) ^-^ !^ ","
            ) ^^
            group @@ separate space (param_typs |> List.map (fun param_typ ->
              group (Type.to_coq (Some subst) (Some Type.Context.Arrow) param_typ ^^ !^ "->")
            )) ^^
            Type.to_coq (Some subst) None (Type.Apply (MixedPath.of_name name, res_typ_params))
          )
        )
      )
    )

  let to_coq_notations_where
    (subst : Type.Subst.t)
    (notation : SmartPrint.t)
    (typ_args : Name.t option list)
    (typ : Type.t)
    : SmartPrint.t =
    let subst = {
      subst with
      Type.Subst.name = fun name ->
        if List.mem (Some name) typ_args then
          Name.prefix_by_t name
        else
          name
    } in
    nest (
      notation ^^ !^ ":=" ^^ parens (
        (match typ_args with
        | [] -> empty
        | _ :: _ ->
          !^ "fun" ^^ parens (
            nest (
              separate space (typ_args |> List.map (fun name ->
                match name with
                | None -> !^ "_"
                | Some name -> Name.to_coq (Name.prefix_by_t name)
              )) ^^
              !^ ":" ^^ Pp.set
            )
          ) ^^ !^ "=>" ^^ space
        ) ^-^ Type.to_coq (Some subst) None typ
      )
    )

  let to_coq_notations_wheres
    (subst : Type.Subst.t)
    (inductive : t)
    : SmartPrint.t list =
    (inductive.notations |> List.map (fun (name, typ_args, typ) ->
      to_coq_notations_where subst (to_coq_notation_name name) typ_args typ
    )) @
    (inductive.constructor_records |> List.map
      (fun (name, records) ->
        records |> List.map (fun ({ RecordSkeleton.module_name; _ }, typ_args, typ) ->
          to_coq_notations_where
            subst
            (to_coq_notation_record name module_name)
            (typ_args |> List.map (fun typ_arg -> Some typ_arg))
            typ
        )
      )
      |> List.concat
    )

  let to_coq_notations_definition (name : Name.t) (definition : SmartPrint.t)
    : SmartPrint.t =
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^ definition ^-^ !^ "."
    )

  let to_coq_notations_record_definitions (inductive : t) : SmartPrint.t option =
    match inductive.constructor_records with
    | [] -> None
    | _ :: _ ->
      let notation_module_name =
        !^ "ConstructorRecordNotations_" ^-^
        separate (!^ "_") (inductive.typs |> List.map (fun (name, _, _) ->
          Name.to_coq name
        )) in
      Some (
        !^ "Module" ^^ notation_module_name ^-^ !^ "." ^^ newline ^^
        indent (separate newline (inductive.constructor_records |> List.map (fun (name, records) ->
          !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
          indent (separate newline (records |> List.map
            (fun ({ RecordSkeleton.module_name; _ }, _, _) ->
              to_coq_notations_definition
                module_name
                (!^ "'" ^-^ Name.to_coq name ^-^ !^ "." ^-^ Name.to_coq module_name)
            )
          )) ^^ newline ^^
          !^ "End" ^^ Name.to_coq name ^-^ !^ "."
        ))) ^^ newline ^^
        !^ "End" ^^ notation_module_name ^-^ !^ "." ^^ newline ^^
        !^ "Import" ^^ notation_module_name ^-^ !^ "."
      )

  let to_coq_notations_definitions (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      to_coq_notations_definition
        name
        (Name.to_coq (Name.prefix_by_single_quote name))
    )

  let to_coq_typs_implicits
    (left_typ_args : Name.t option list)
    (constructors : Constructors.t)
    : SmartPrint.t list =
    match left_typ_args with
    | [] -> []
    | _ :: _ ->
      constructors |> List.map (fun { Constructors.constructor_name; typ_vars; _ } ->
        !^ "Arguments" ^^ Name.to_coq constructor_name ^^ braces (
          nest (
            separate space (
              (left_typ_args |> List.map (fun _ -> !^ "_")) @
              (typ_vars |> List.map (fun _ -> !^ "_"))
            )
          )
        ) ^-^ !^ "."
      )

  let to_coq (inductive : t) : SmartPrint.t =
    let subst = {
      Type.Subst.name = (fun name -> name);
      path_name = fun path_name ->
        match path_name with
        | { PathName.path = []; base } ->
          let use_notation =
            inductive.notations |> List.exists (fun (name, _, _) ->
              name = base
            ) in
          if use_notation then
            { path = []; base = Name.prefix_by_single_quote base }
          else
            path_name
        | { path = [prefix]; base } ->
          let use_notation =
            inductive.constructor_records |> List.exists (fun (name, records) ->
              records |> List.exists
                (fun ({ RecordSkeleton.module_name; _ }, _, _) ->
                  name = prefix && module_name = base
                )
            ) in
          if use_notation then
            { path = [Name.prefix_by_single_quote prefix]; base }
          else
            path_name
        | _ -> path_name
    } in
    let constructor_records = to_coq_constructor_records inductive in
    let record_skeletons = to_coq_record_skeletons inductive in
    let reserved_notations = to_coq_notations_reserved inductive in
    let notations_wheres = to_coq_notations_wheres subst inductive in
    let notations_record_definitions = to_coq_notations_record_definitions inductive in
    let notations_definitions = to_coq_notations_definitions inductive in
    let implicit_arguments =
      List.concat (inductive.typs |> List.map (fun (_, left_typ_args, constructors) ->
        to_coq_typs_implicits left_typ_args constructors
      )) in
    nest (
      (match constructor_records with
      | [] -> empty
      | _ :: _ -> separate (newline ^^ newline) constructor_records ^^ newline ^^ newline) ^^
      (match record_skeletons with
      | [] -> empty
      | _ :: _ -> separate (newline ^^ newline) record_skeletons ^^ newline ^^ newline) ^^
      (match reserved_notations with
      | [] -> empty
      | _ :: _ -> separate newline reserved_notations ^^ newline ^^ newline) ^^
      separate (newline ^^ newline) (inductive.typs |>
        List.mapi (fun index (name, left_typ_args, constructors) ->
          let is_first = index = 0 in
          to_coq_typs subst is_first name left_typ_args constructors
        )
      ) ^-^
      (match notations_wheres with
      | [] -> empty
      | _ :: _ ->
        newline ^^ newline ^^
        !^ "where " ^-^ separate (newline ^^ !^ "and ") notations_wheres
      ) ^-^ !^ "." ^^
      (match notations_record_definitions with
      | None -> empty
      | Some notations -> newline ^^ newline ^^ notations) ^^
      (match notations_definitions with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline notations_definitions) ^^
      (match implicit_arguments with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline implicit_arguments)
    )
end

type t =
  | Inductive of Inductive.t
  | Record of Name.t * Name.t list * (Name.t * Type.t) list
  | Synonym of Name.t * Name.t list * Type.t
  | Abstract of Name.t * Name.t list

let of_ocaml (typs : type_declaration list) : t Monad.t =
  match typs with
  | [ { typ_id; typ_type = { type_kind = Type_record (fields, _); type_params; _ }; _ } ] ->
    let name = Name.of_ident false typ_id in
    (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (Name.of_ident false x, typ)
    )) >>= fun fields ->
    return (Record (name, typ_args, fields))
  | [ { typ_id; typ_type = { type_kind = Type_abstract; type_manifest; type_params; _ }; _ } ] ->
    let name = Name.of_ident false typ_id in
    named_typ_params_expecting_variables type_params >>= fun typ_args ->
    let typ_args_with_unknowns = named_typ_params_with_unknowns typ_args in
    begin match type_manifest with
    | Some typ ->
      begin match typ.Types.desc with
      | Tvariant { row_fields; _ } ->
        Monad.List.map
          (Constructors.Single.of_ocaml_row typ_args)
          row_fields >>= fun single_constructors ->
        Constructors.of_ocaml name typ_args single_constructors >>= fun (constructors, _) ->
        raise
          (Inductive {
            constructor_records = [];
            notations = [];
            records = [];
            typs = [(name, typ_args, constructors)];
          })
          NotSupported
          "Polymorphic variant types are not handled"
      | _ ->
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return (Synonym (name, typ_args_with_unknowns, typ))
      end
    | None -> return (Abstract (name, typ_args_with_unknowns))
    end
  | [ { typ_id; typ_type = { type_kind = Type_open; _ }; _ } ] ->
    let name = Name.of_ident false typ_id in
    let typ = Type.Apply (MixedPath.of_name (Name.of_string false "extensible_type"), []) in
    raise (Synonym (name, [], typ)) NotSupported "Extensible types are not handled"
  | _ ->
    (typs |> Monad.List.fold_left (fun (constructor_records, notations, records, typs) typ ->
      set_loc (Loc.of_location typ.typ_loc) (
      let name = Name.of_ident false typ.typ_id in
      named_typ_params_expecting_variables typ.typ_type.type_params >>= fun typ_args ->
      match typ with
      | { typ_type = { type_kind = Type_abstract; type_manifest = Some typ; _ }; _ } ->
        begin match typ.Types.desc with
        | Tvariant { row_fields; _ } ->
          Monad.List.map (Constructors.Single.of_ocaml_row typ_args) row_fields >>= fun single_constructors ->
          Constructors.of_ocaml name typ_args single_constructors >>= fun (constructors, _) ->
          raise
            (
              constructor_records,
              notations,
              records,
              (name, typ_args, constructors) :: typs
            )
            NotSupported
            "Polymorphic variant types are not handled"
        | _ ->
          Type.of_type_expr_without_free_vars typ >>= fun typ ->
          return (
            constructor_records,
            (
              name,
              typ_args,
              typ
            ) :: notations,
            records,
            typs
          )
        end
      | { typ_type = { type_kind = Type_abstract; type_manifest = None; _ }; _ } ->
        raise
          (constructor_records, notations, records, typs)
          NotSupported
          "Abstract types not supported in mutually recursive definitions"
      | { typ_type = { type_kind = Type_record (fields, _); type_params; _ }; _ } ->
        (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
          Type.of_type_expr_without_free_vars typ >>= fun typ ->
          return (Name.of_ident false x, typ)
        )) >>= fun fields ->
        named_typ_params_expecting_variables type_params >>= fun typ_args ->
        return (
          constructor_records,
          (
            name,
            typ_args,
            Type.Apply (
              MixedPath.of_name (Name.suffix_by_skeleton name),
              fields |> List.map snd
            )
          ) :: notations,
          {
            RecordSkeleton.fields = fields |> List.map fst;
            module_name = name;
            typ_name = Name.suffix_by_skeleton name;
           } :: records,
          typs
        )
      | { typ_type = { type_kind = Type_variant cases; _ }; _ } ->
        Monad.List.map (Constructors.Single.of_ocaml_case name typ_args) cases >>= fun cases ->
        let (single_constructors, new_constructor_records) = List.split cases in
        let new_constructor_records =
          new_constructor_records |> Util.List.filter_map (fun x -> x) in
        let constructor_records =
          match new_constructor_records with
          | [] -> constructor_records
          | _ :: _ ->
            (name, new_constructor_records) :: constructor_records in
        Constructors.of_ocaml
          name
          typ_args
          single_constructors >>= fun (constructors, merged_typ_params) ->
        let (gadt_notation, name, typ_args) =
          match merged_typ_params with
          | None ->
            (
              [(
                name,
                typ_args |> List.map (fun _ -> None),
                Constructors.gadt_typ name
              )],
              Name.suffix_by_gadt name,
              []
            )
          | Some merged_typ_params ->
            (
              [],
              name,
              merged_typ_params
            ) in
        return (
          constructor_records,
          gadt_notation @ notations,
          records,
          (name, typ_args, constructors) :: typs
        )
      | { typ_type = { type_kind = Type_open; _ }; _ } ->
        raise
          (constructor_records, notations, records, typs)
          NotSupported
          "Extensible types are not handled"
      )
    ) ([], [], [], [])) >>= fun (constructor_records, notations, records, typs) ->
    return (
      Inductive {
        constructor_records = List.rev constructor_records;
        notations = List.rev notations;
        records;
        typs = List.rev typs
      }
    )

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive inductive -> Inductive.to_coq inductive
  | Record (name, typ_args, fields) ->
    to_coq_record true name name typ_args fields
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      begin match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set)
      end ^^
      !^ ":=" ^^ Type.to_coq None None value ^-^ !^ "."
    )
  | Abstract (name, typ_args) ->
    nest (
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ parens (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ Pp.set)) ^-^ !^ ",") ^^
      Pp.set ^-^ !^ ".")
