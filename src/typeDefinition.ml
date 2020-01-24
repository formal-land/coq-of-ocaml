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
      !^ ":=" ^^ !^ "{" ^^ newline ^^
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
          let suffixed_typ_args =
            typ_args |> List.map (fun typ_arg ->
              Name.to_coq (Name.suffix_by_type typ_arg)
             ) in
          let record_typ =
            nest (separate space (!^ "record" :: suffixed_typ_args)) in
          nest (
            !^ "Definition" ^^ Name.to_coq (Name.prefix_by_with name) ^^
            begin match typ_args with
            | [] -> empty
            | _ :: _ ->
              braces (nest (
                separate space suffixed_typ_args ^^
                !^ ":" ^^ Pp.set
              ))
            end ^^
            nest (parens (!^ "r" ^^ !^ ":" ^^ record_typ)) ^^
            Name.to_coq name ^^
            nest (!^ ":" ^^ record_typ ^^ !^ ":=") ^^ newline ^^
            indent @@ nest (
              !^ "{|" ^^
              separate (!^ ";" ^^ space) (fields |> List.map (fun (name', _) ->
                nest (
                  Name.to_coq name' ^-^ !^ " :=" ^^
                  if Name.equal name name' then
                    Name.to_coq name
                  else
                    Name.to_coq name' ^^ !^ "r"
                )
              )) ^^
              !^ "|}" ^-^ !^ "."
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
      is_gadt : bool;
      param_typs : Type.t list; (** The parameters of the constructor. *)
    }

    let of_ocaml_case (typ_name : Name.t) (case : Types.constructor_declaration)
      : (t * RecordSkeleton.t option) Monad.t =
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
        return (
          [
            Type.Apply (
              MixedPath.PathName {
                path = [typ_name];
                base = constructor_name;
              },
              record_params
            )
          ],
          Some {
            RecordSkeleton.fields = record_fields;
            module_name = constructor_name;
            typ_name = constructor_name;
          }
        ))
      end >>= fun (param_typs, records) ->
      let is_gadt = match cd_res with None -> false | Some _ -> true in
      return (
        {
          constructor_name;
          is_gadt;
          param_typs;
        },
        records
      ))

    let of_ocaml_row (row : Asttypes.label * Types.row_field) : t Monad.t =
      let (label, field) = row in
      let typs = Type.type_exprs_of_row_field field in
      Type.of_typs_exprs true Name.Map.empty typs >>= fun (param_typs, _, _) ->
      return {
        constructor_name = Name.of_string false label;
        is_gadt = false;
        param_typs;
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
    | Forall (name, param, result) ->
      Forall (
        name,
        subst_gadt_typ_constructor typ_name param,
        if Name.equal typ_name name then
          result
        else
          subst_gadt_typ_constructor typ_name result
      )
    | Error _ -> typ

  let of_ocaml
    (typ_name : Name.t)
    (defined_typ_params : Name.t list)
    (single_constructors : Single.t list)
    : (t * bool) Monad.t =
    let is_gadt =
      List.exists (fun { Single.is_gadt; _ } -> is_gadt) single_constructors in
    let constructors = single_constructors |> List.map (
      fun { Single.constructor_name; param_typs; _ } ->
        if is_gadt then
          let param_typs =
            param_typs |> List.map (subst_gadt_typ_constructor typ_name) in
          {
            constructor_name;
            param_typs;
            res_typ_params = [];
            typ_vars = Name.Set.elements (Type.typ_args_of_typs param_typs)
          }
        else
          {
            constructor_name;
            param_typs;
            res_typ_params =
              List.map (fun name -> Type.Variable name) defined_typ_params;
            typ_vars =
              Name.Set.elements (
                Name.Set.diff
                  (Type.typ_args_of_typs param_typs)
                  (Name.Set.of_list defined_typ_params)
              )
          }
    ) in
    return (constructors, is_gadt)
end

module Inductive = struct
  type t = {
    constructor_records : (Name.t * RecordSkeleton.t list) list;
    notations : (Name.t * Name.t list * Type.t) list;
    records : RecordSkeleton.t list;
    typs : (Name.t * Name.t list * Constructors.t) list;
  }

  let to_coq_constructor_records (inductive : t) : SmartPrint.t list =
    inductive.constructor_records |> List.map (fun (name, records) ->
      !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
      indent (
        separate
          (newline ^^ newline)
          (List.map (RecordSkeleton.to_coq false) records)
      ) ^^ newline ^^
      !^ "End" ^^ Name.to_coq name ^-^ !^ "."
    )

  let to_coq_notations_reserved (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      !^ "Reserved Notation" ^^ !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\"" ^-^ !^ "."
    )

  let to_coq_record_skeletons (inductive : t) : SmartPrint.t list =
    inductive.records |> List.map (RecordSkeleton.to_coq true)

  let to_coq_typs
    (subst : (Name.t -> Name.t) option)
    (is_first : bool)
    (name : Name.t)
    (left_typ_args : Name.t list)
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
            separate space (List.map Name.to_coq left_typ_args) ^^
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
              group (Type.to_coq subst (Some Type.Context.Arrow) param_typ ^^ !^ "->")
            )) ^^ Type.to_coq subst None (Type.Apply (MixedPath.of_name name, res_typ_params))
          )
        )
      )
    )

  let to_coq_notations_wheres
    (subst : (Name.t -> Name.t) option)
    (inductive : t)
    : SmartPrint.t list =
    inductive.notations |> List.mapi (fun index (name, typ_args, value) ->
      let is_first = index = 0 in
      nest (
        !^ (if is_first then "where" else "and") ^^
        !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\"" ^^ !^ ":=" ^^ parens (
          (match typ_args with
          | [] -> empty
          | _ :: _ ->
            !^ "fun" ^^ parens (
              nest (
                separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
              )
            ) ^^ !^ "=>" ^^ space
          ) ^-^ Type.to_coq subst None value
        )
      )
    )

  let to_coq_notations_definitions (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^ !^ "'" ^-^ Name.to_coq name ^-^ !^ "."
      )
    )

  let to_coq_typs_implicits
    (left_typ_args : Name.t list)
    (constructors : Constructors.t)
    : SmartPrint.t list =
    match left_typ_args with
    | [] -> []
    | _ :: _ ->
      constructors |> List.map (fun { Constructors.constructor_name; _ } ->
        !^ "Arguments" ^^ Name.to_coq constructor_name ^^ braces (
          nest (
            separate space (left_typ_args |> List.map (fun _ -> !^ "_"))
          )
        ) ^-^ !^ "."
      )

  let to_coq (inductive : t) : SmartPrint.t =
    let subst = Some (fun name ->
      match inductive.notations |> List.find_opt (fun (name', _, _) -> name' = name) with
      | None -> name
      | Some (name', _, _) -> Name.prefix_by_single_quote name'
    ) in
    let constructor_records = to_coq_constructor_records inductive in
    let reserved_notations = to_coq_notations_reserved inductive in
    let record_skeletons = to_coq_record_skeletons inductive in
    let notation_wheres = to_coq_notations_wheres subst inductive in
    let notation_definitions = to_coq_notations_definitions inductive in
    let implicit_arguments =
      List.concat (inductive.typs |> List.map (fun (_, left_typ_args, constructors) ->
        to_coq_typs_implicits left_typ_args constructors
      )) in
    nest (
      (match constructor_records with
      | [] -> empty
      | _ :: _ -> separate (newline ^^ newline) constructor_records ^^ newline ^^ newline) ^^
      (match reserved_notations with
      | [] -> empty
      | _ :: _ -> separate newline reserved_notations ^^ newline ^^ newline) ^^
      (match record_skeletons with
      | [] -> empty
      | _ :: _ -> separate (newline ^^ newline) record_skeletons ^^ newline ^^ newline) ^^
      separate (newline ^^ newline) (inductive.typs |>
        List.mapi (fun index (name, left_typ_args, constructors) ->
          let is_first = index = 0 in
          to_coq_typs subst is_first name left_typ_args constructors
        )
      ) ^-^
      (match notation_wheres with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline notation_wheres) ^-^ !^ "." ^^
      (match notation_definitions with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline notation_definitions) ^^
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
    (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    begin match type_manifest with
    | Some typ ->
      begin match typ.Types.desc with
      | Tvariant { row_fields; _ } ->
        Monad.List.map Constructors.Single.of_ocaml_row row_fields >>= fun single_constructors ->
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
        return (Synonym (name, typ_args, typ))
      end
    | None -> return (Abstract (name, typ_args))
    end
  | [ { typ_id; typ_type = { type_kind = Type_open; _ }; _ } ] ->
    let name = Name.of_ident false typ_id in
    let typ = Type.Apply (MixedPath.of_name (Name.of_string false "extensible_type"), []) in
    raise (Synonym (name, [], typ)) NotSupported "Extensible types are not handled"
  | _ ->
    (typs |> Monad.List.fold_left (fun (constructor_records, notations, records, typs) typ ->
      set_loc (Loc.of_location typ.typ_loc) (
      let name = Name.of_ident false typ.typ_id in
      (typ.typ_type.type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      match typ with
      | { typ_type = { type_kind = Type_abstract; type_manifest = Some typ; _ }; _ } ->
        begin match typ.Types.desc with
        | Tvariant { row_fields; _ } ->
          Monad.List.map Constructors.Single.of_ocaml_row row_fields >>= fun single_constructors ->
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
            (name, typ_args, typ) :: notations,
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
        (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
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
        Monad.List.map (Constructors.Single.of_ocaml_case name) cases >>= fun cases ->
        let (single_constructors, new_constructor_records) = List.split cases in
        let new_constructor_records =
          new_constructor_records |> Util.List.filter_map (fun x -> x) in
        let constructor_records =
          match new_constructor_records with
          | [] -> constructor_records
          | _ :: _ -> (name, new_constructor_records) :: constructor_records in
        Constructors.of_ocaml name typ_args single_constructors >>= fun (constructors, is_gadt) ->
        let gadt_notation =
          if is_gadt then
            [(name, typ_args, Constructors.gadt_typ name)]
          else
            [] in
        let name = if is_gadt then Name.suffix_by_gadt name else name in
        let typ_args = if is_gadt then [] else typ_args in
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
