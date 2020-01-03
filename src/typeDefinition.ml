open Typedtree
open SmartPrint
open Monad.Notations

let to_coq_record
  (name : Name.t)
  (typ_args : Name.t list)
  (fields : (Name.t * Type.t) list)
  : SmartPrint.t =
  nest (
    !^ "Record" ^^ Name.to_coq name ^^
    (match typ_args with
    | [] -> empty
    | _ :: _ ->
      braces (nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type"
      ))
    ) ^^
    !^ ":=" ^^ !^ "{" ^^ newline ^^
    indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
      nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None typ)))) ^^
    !^ "}." ^^
    (match typ_args with
    | [] -> empty
    | _ :: _ ->
      newline ^^ !^ "Arguments" ^^ Name.to_coq name ^^ !^ ":" ^^ !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
    )
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
      is_gadt : bool;
      param_typs : Type.t list; (** The parameters of the constructor. *)
    }

    let of_ocaml (case : Types.constructor_declaration)
      : t Monad.t =
      let { Types.cd_args; cd_id; cd_loc; cd_res; _ } = case in
      set_loc (Loc.of_location cd_loc) (
      let constructor_name = Name.of_ident cd_id in
      let typ_vars = Name.Map.empty in
      (match cd_args with
      | Cstr_tuple param_typs -> Type.of_typs_exprs true typ_vars param_typs
      | Cstr_record labeled_typs ->
        set_loc (Loc.of_location cd_loc) (
        (
          labeled_typs |>
          List.map (fun { Types.ld_type; _ } -> ld_type) |>
          Type.of_typs_exprs true typ_vars
        ) >>= fun result ->
        raise result NotSupported "Unhandled named constructor parameters.")
      ) >>= fun (param_typs, _, _) ->
      let is_gadt = match cd_res with None -> false | Some _ -> true in
      return {
        constructor_name;
        is_gadt;
        param_typs;
      })
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

  let of_ocaml
    (typ_name : Name.t)
    (defined_typ_params : Name.t list)
    (cases : Types.constructor_declaration list)
    : (t * bool) Monad.t =
    Monad.List.map Single.of_ocaml cases >>= fun single_constructors ->
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
    notations : (Name.t * Name.t list * Type.t) list;
    records : (Name.t * Name.t list) list;
    typs : (Name.t * Name.t list * Constructors.t) list;
  }

  let to_coq_notations_reserved (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      !^ "Reserved Notation" ^^ !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\"" ^-^ !^ "."
    )

  let to_coq_record_skeletons (inductive : t) : SmartPrint.t list =
    inductive.records |> List.map (fun (name, fields) ->
      to_coq_record name fields (fields |> List.map (fun field -> (field, Type.Variable field)))
    )

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
            !^ ":" ^^ !^ "Type"
          )
        )
      ) ^^ !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^-^
      separate empty (
        constructors |> List.map (fun { Constructors.constructor_name; param_typs; res_typ_params; typ_vars } ->
          newline ^^ nest (
            !^ "|" ^^ Name.to_coq constructor_name ^^ !^ ":" ^^
            (match typ_vars with
            | [] -> empty
            | _ ->
              !^ "forall" ^^ braces (
                separate space (typ_vars |> List.map Name.to_coq) ^^ !^ ":" ^^ !^ "Type"
              ) ^-^ !^ ","
            ) ^^
            separate space (param_typs |> List.map (fun param_typ ->
              Type.to_coq subst (Some Type.Context.Arrow) param_typ ^^ !^ "->"
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
                separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type"
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
    let reserved_notations = to_coq_notations_reserved inductive in
    let record_skeletons = to_coq_record_skeletons inductive in
    let notation_wheres = to_coq_notations_wheres subst inductive in
    let notation_definitions = to_coq_notations_definitions inductive in
    let implicit_arguments =
      List.concat (inductive.typs |> List.map (fun (_, left_typ_args, constructors) ->
        to_coq_typs_implicits left_typ_args constructors
      )) in
    nest (
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
    let name = Name.of_ident typ_id in
    (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (Name.of_ident x, typ)
    )) >>= fun fields ->
    return (Record (name, typ_args, fields))
  | [ { typ_id; typ_type = { type_kind = Type_abstract; type_manifest; type_params; _ }; _ } ] ->
    let name = Name.of_ident typ_id in
    (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    begin match type_manifest with
    | Some typ ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (Synonym (name, typ_args, typ))
    | None -> return (Abstract (name, typ_args))
    end
  | [ { typ_id; typ_type = { type_kind = Type_open; _ }; _ } ] ->
    let name = Name.of_ident typ_id in
    let typ = Type.Apply (MixedPath.of_name (Name.of_string "False"), []) in
    raise (Synonym (name, [], typ)) NotSupported "Extensible types are not handled"
  | _ ->
    (typs |> Monad.List.fold_left (fun (notations, records, typs) typ ->
      set_loc (Loc.of_location typ.typ_loc) (
      let name = Name.of_ident typ.typ_id in
      (typ.typ_type.type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      match typ with
      | { typ_type = { type_kind = Type_abstract; type_manifest = Some typ; _ }; _ } ->
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return ((name, typ_args, typ) :: notations, records, typs)
      | { typ_type = { type_kind = Type_abstract; type_manifest = None; _ }; _ } ->
        raise
          (notations, records, typs)
          NotSupported
          "Abstract types not supported in mutually recursive definitions"
      | { typ_type = { type_kind = Type_record (fields, _); type_params; _ }; _ } ->
        (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
          Type.of_type_expr_without_free_vars typ >>= fun typ ->
          return (Name.of_ident x, typ)
        )) >>= fun fields ->
        (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
        return (
          (
            name,
            typ_args,
            Type.Apply (
              MixedPath.of_name (Name.suffix_by_skeleton name),
              fields |> List.map snd
            )
          ) :: notations,
          (
            Name.suffix_by_skeleton name,
            fields |> List.map fst
          ) :: records,
          typs
        )
      | { typ_type = { type_kind = Type_variant cases; _ }; _ } ->
        Constructors.of_ocaml name typ_args cases >>= fun (constructors, is_gadt) ->
        let gadt_notation =
          if is_gadt then
            [(name, typ_args, Constructors.gadt_typ name)]
          else
            [] in
        let name = if is_gadt then Name.suffix_by_gadt name else name in
        let typ_args = if is_gadt then [] else typ_args in
        return (
          gadt_notation @ notations,
          records,
          (name, typ_args, constructors) :: typs
        )
      | { typ_type = { type_kind = Type_open; _ }; _ } ->
        raise
          (notations, records, typs)
          NotSupported
          "Extensible types are not handled"
      )
    ) ([], [], [])) >>= fun (notations, records, typs) ->
    return (Inductive { notations = List.rev notations; records; typs = List.rev typs })

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive inductive -> Inductive.to_coq inductive
  | Record (name, typ_args, fields) -> to_coq_record name typ_args fields
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      begin match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type")
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
          !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      !^ "Type" ^-^ !^ ".")
