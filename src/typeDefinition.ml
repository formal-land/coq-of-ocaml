open Typedtree
open Sexplib.Std
open SmartPrint
open Monad.Notations

(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
module Constructors = struct
  (** [constructor_name]: forall [typ_vars], [param_typs] -> t [res_typ_params] *)
  type item = {
    constructor_name : Name.t;
    param_typs : Type.t list; (** The parameters of the constructor. *)
    res_typ_params : Type.t list; (** The type parameters of the result type of the constructor. *)
    typ_vars : Name.t list; (** The polymorphic type variables. *)
  } [@@deriving sexp]

  type t = item list
    [@@deriving sexp]

  let of_ocaml
    (defined_typ_params : Name.t list)
    (cases : Types.constructor_declaration list)
    : t Monad.t =
    cases |> Monad.List.map (fun { Types.cd_args; cd_id; cd_loc; cd_res; _ } ->
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
      ) >>= fun (param_typs, typ_vars, new_typ_vars_params) ->
      (match cd_res with
      | None ->
        return (
          List.map (fun name -> Type.Variable name) defined_typ_params,
          Name.Set.of_list defined_typ_params
        )
      | Some res_typ ->
        Type.of_typ_expr true typ_vars res_typ >>= fun (res_typ, _, new_typ_vars) ->
        begin match res_typ with
        | Type.Apply (_, res_typ_params) -> return (res_typ_params, new_typ_vars)
        | _ -> raise ([], Name.Set.empty) Unexpected "Expected an applied type as return type"
        end
      ) >>= fun (res_typ_params, new_typ_vars_res) ->
      return {
        constructor_name;
        param_typs;
        res_typ_params;
        typ_vars = Name.Set.elements (Name.Set.union new_typ_vars_params new_typ_vars_res);
      })
    )

  let remove_typ_var (typ_var : Name.t) (constructors : t) : t =
    constructors |> List.map (fun constructor ->
      { constructor with
        typ_vars = constructor.typ_vars |> List.filter (fun typ_var' -> typ_var' <> typ_var)
      }
    )

  let extract_common_typ_args (typ_args : Name.t list) (constructors : t) : Name.t list * Name.t list * t =
    let (left_typ_args, right_typ_args, constructors) =
      typ_args |>
      List.mapi (fun index typ_arg -> (index, typ_arg)) |>
      List.fold_left (fun (left_typ_args, right_typ_args, constructors) (index, typ_arg) ->
        let is_typ_arg_common =
          constructors |> List.for_all (fun constructor ->
            match List.nth_opt constructor.res_typ_params index with
            | Some (Type.Variable typ_arg') -> typ_arg = typ_arg'
            | _ -> false
          ) in
        if is_typ_arg_common then
          (typ_arg :: left_typ_args, right_typ_args, remove_typ_var typ_arg constructors)
        else
          (left_typ_args, typ_arg :: right_typ_args, constructors)
      ) ([], [], constructors) in
    (List.rev left_typ_args, List.rev right_typ_args, constructors)
end

module Inductive = struct
  type t = {
    notations : (Name.t * Name.t list * Type.t) list;
    typs : (Name.t * Name.t list * Name.t list * Constructors.t) list;
  } [@@deriving sexp]

  let to_coq_notations_reserved (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      !^ "Reserved Notation" ^^ !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\"" ^-^ !^ "."
    )

  let to_coq_typs
    (subst : (Name.t -> Name.t) option)
    (is_first : bool)
    (name : Name.t)
    (left_typ_args : Name.t list)
    (right_typ_args : Name.t list)
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
      ) ^^ !^ ":" ^^
      (if right_typ_args = [] then
        empty
      else
        !^ "forall" ^^
        parens (
          nest (
            separate space (List.map Name.to_coq right_typ_args) ^^
            !^ ":" ^^ !^ "Type"
          )
        ) ^-^ !^ ","
      ) ^^ !^ "Type" ^^ !^ ":=" ^-^
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
              Type.to_coq subst true param_typ ^^ !^ "->"
            )) ^^ Type.to_coq subst false (Type.Apply (MixedPath.of_name name, res_typ_params))
          )
        )
      )
    )

  let to_coq_notations_wheres (subst : (Name.t -> Name.t) option) (inductive : t) : SmartPrint.t list =
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
            ) ^^ !^ "=>"
          ) ^^ Type.to_coq subst false value
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
      | Some (name', _, _) -> "'" ^ name'
    ) in
    let reserved_notations = to_coq_notations_reserved inductive in
    let implicit_arguments =
      List.concat (inductive.typs |> List.map (fun (_, left_typ_args, _, constructors) ->
        to_coq_typs_implicits left_typ_args constructors
      )) in
    let notation_wheres = to_coq_notations_wheres subst inductive in
    let notation_definitions = to_coq_notations_definitions inductive in
    nest (
      (match reserved_notations with
      | [] -> empty
      | _ :: _ -> separate newline reserved_notations ^^ newline ^^ newline) ^^
      separate (newline ^^ newline) (inductive.typs |>
        List.mapi (fun index (name, left_typ_args, right_typ_args, constructors) ->
          let is_first = index = 0 in
          to_coq_typs subst is_first name left_typ_args right_typ_args constructors
        )
      ) ^-^
      (match notation_wheres with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate (newline ^^ newline) notation_wheres) ^-^ !^ "." ^^
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
  [@@deriving sexp]

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
    let typ = Type.Apply (MixedPath.of_name "False", []) in
    raise (Synonym (name, [], typ)) NotSupported "Extensible types are not handled"
  | _ ->
    (typs |> Monad.List.fold_left (fun (notations, typs) typ ->
      set_loc (Loc.of_location typ.typ_loc) (
      let name = Name.of_ident typ.typ_id in
      (typ.typ_type.type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      match typ with
      | { typ_type = { type_kind = Type_abstract; type_manifest = Some typ; _ }; _ } ->
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return ((name, typ_args, typ) :: notations, typs)
      | { typ_type = { type_kind = Type_variant cases; _ }; _ } ->
        Constructors.of_ocaml typ_args cases >>= fun constructors ->
        return (notations, (name, typ_args, constructors) :: typs)
      | _ ->
        raise
          (notations, typs)
          NotSupported
          "Only algebraic or synonym types are supported in mutually recursive types"
      )
    ) ([], [])) >>= fun (notations, typs) ->
    let typs = typs |> List.map (fun (name, typ_args, constructors) ->
      let (left_typ_args, right_typ_args, constructors) =
        Constructors.extract_common_typ_args typ_args constructors in
      (name, left_typ_args, right_typ_args, constructors)
    ) in
    return (Inductive { notations = List.rev notations; typs = List.rev typs })

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive inductive -> Inductive.to_coq inductive
  | Record (name, typ_args, fields) ->
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
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None false typ)))) ^^
      !^ "}." ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        newline ^^ !^ "Arguments" ^^ Name.to_coq name ^^ !^ ":" ^^ !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
      )
    )
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      (match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type")) ^^
      !^ ":=" ^^ Type.to_coq None false value ^-^ !^ "."
    )
  | Abstract (name, typ_args) ->
    nest (
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      !^ "Type" ^-^ !^ ".")
