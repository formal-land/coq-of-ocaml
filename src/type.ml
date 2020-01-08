(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint
open Monad.Notations

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Sum of (string * t) list
  | Tuple of t list
  | Apply of MixedPath.t * t list
  | Package of PathName.t * t option Tree.t

let type_exprs_of_row_field (row_field : Types.row_field) : Types.type_expr list =
  match row_field with
  | Rpresent None -> []
  | Rpresent (Some typ) -> [typ]
  | Reither (_, typs, _, _) -> typs
  | Rabsent -> []

(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_typ_expr
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * Name.Set.t) Monad.t =
  match typ.desc with
  | Tvar x | Tunivar x ->
    (match x with
    | None ->
      if with_free_vars then
        let n = Name.Map.cardinal typ_vars in
        return (Printf.sprintf "A%d" typ.id, String.make 1 (Char.chr (Char.code 'A' + n)))
      else
        raise ("_", "_") NotSupported "The placeholders `_` in types are not handled"
    | Some x -> return (x, x)
    ) >>= fun (source_name, generated_name) ->
    let source_name = Name.of_string false source_name in
    let generated_name = Name.of_string false generated_name in
    let (typ_vars, new_typ_vars, name) =
      if Name.Map.mem source_name typ_vars then (
        let name = Name.Map.find source_name typ_vars in
        (typ_vars, Name.Set.empty, name)
      ) else (
        let typ_vars = Name.Map.add source_name generated_name typ_vars in
        (typ_vars, Name.Set.singleton generated_name, generated_name)
      ) in
    return (Variable name, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    of_typ_expr with_free_vars typ_vars typ_x >>= fun (typ_x, typ_vars, new_typ_vars_x) ->
    of_typ_expr with_free_vars typ_vars typ_y >>= fun (typ_y, typ_vars, new_typ_vars_y) ->
    return (Arrow (typ_x, typ_y), typ_vars, Name.Set.union new_typ_vars_x new_typ_vars_y)
  | Ttuple typs ->
    of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    return (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    MixedPath.of_path false path None >>= fun mixed_path ->
    return (Apply (mixed_path, typs), typ_vars, new_typ_vars)
  | Tobject (typ, params) ->
    of_typ_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars) ->
    (match !params with
    | None -> return ([], typ_vars, new_typ_vars)
    | Some (_, typs) ->
      of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars_params) ->
      return (typs, typ_vars, Name.Set.union new_typ_vars new_typ_vars_params)
    ) >>= fun (typs, typ_vars, new_typ_vars) ->
    raise (Tuple (typ :: typs), typ_vars, new_typ_vars) NotSupported "Object types are not handled"
  | Tfield (_, _, typ1, typ2) ->
    of_typ_expr with_free_vars typ_vars typ1 >>= fun (typ1, typ_vars, new_typ_vars1) ->
    of_typ_expr with_free_vars typ_vars typ2 >>= fun (typ2, typ_vars, new_typ_vars2) ->
    raise
      (
        Tuple [typ1; typ2],
        typ_vars,
        Name.Set.union new_typ_vars1 new_typ_vars2
      )
      NotSupported "Field types are not handled"
  | Tnil ->
    raise
      (Variable (Name.of_string false "nil"), typ_vars, Name.Set.empty)
      NotSupported
      "Nil type is not handled"
  | Tlink typ | Tsubst typ -> of_typ_expr with_free_vars typ_vars typ
  | Tvariant { row_fields; _ } ->
    Monad.List.fold_left
      (fun (fields, typ_vars, new_typ_vars) (name, row_field) ->
        let typs = type_exprs_of_row_field row_field in
        of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars') ->
        return (
          (name, Tuple typs) :: fields,
          typ_vars,
          Name.Set.union new_typ_vars new_typ_vars'
        )
      )
      ([], typ_vars, Name.Set.empty)
      row_fields >>= fun (fields, typ_vars, new_typ_vars) ->
    raise
      (Sum (List.rev fields), typ_vars, new_typ_vars)
      NotSupported
      "Polymorphic variant types are not handled"
  | Tpoly (typ, []) -> of_typ_expr with_free_vars typ_vars typ
  | Tpoly (typ, typs) ->
    of_typ_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars_typ) ->
    of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars_typs) ->
    raise
      (Tuple [typ; Tuple typs], typ_vars, Name.Set.union new_typ_vars_typ new_typ_vars_typs)
      NotSupported
      "Forall quantifier is not handled"
  | Tpackage (path, idents, typs) ->
      let path_name = PathName.of_path_without_convert false path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let path_name = PathName.of_long_ident false ident in
          of_typ_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
          return (
            (path_name, typ) :: typ_substitutions,
            typ_vars,
            Name.Set.union new_typ_vars new_typ_vars'
          )
        )
        ([], typ_vars, Name.Set.empty)
        typ_substitutions >>= fun (typ_substitutions, typ_vars, new_typ_vars) ->
      get_env >>= fun env ->
      let module_typ = Env.find_modtype path env in
      ModuleTypParams.get_module_typ_declaration_typ_params module_typ >>= fun signature_typ_params ->
      let typ_params = List.fold_left
        (fun typ_values (path_name, typ) ->
          Tree.map_at typ_values path_name (fun _ -> Some typ)
        )
        (signature_typ_params |> Tree.map (fun _ -> None))
        typ_substitutions in
      return (Package (path_name, typ_params), typ_vars, new_typ_vars)

and of_typs_exprs
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * Name.Set.t) Monad.t =
  (Monad.List.fold_left
    (fun (typs, typ_vars, new_typ_vars) typ ->
      of_typ_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
      return (typ :: typs, typ_vars, Name.Set.union new_typ_vars new_typ_vars')
    )
    ([], typ_vars, Name.Set.empty)
    typs
  ) >>= fun (typs, typ_vars, new_typ_vars) ->
  return (List.rev typs, typ_vars, new_typ_vars)

let of_type_expr_without_free_vars (typ : Types.type_expr) : t Monad.t =
  of_typ_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
  return typ

let of_type_expr_variable (typ : Types.type_expr) : Name.t Monad.t =
  match typ.desc with
  | Tvar (Some x) -> return (Name.of_string false x)
  | _ ->
    raise
      (Name.of_string false "expected_variable")
      NotSupported
      "Only type variables are supported as parameters"

(** The free variables of a type. *)
let rec typ_args (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Sum typs -> typ_args_of_typs (List.map snd typs)
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Package (_, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | None -> None
      | Some typ -> Some (typ_args typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args typ))
    Name.Set.empty typs

(** In a function's type extract the body's type (up to [n] arguments). *)
let rec open_type (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ1, typ2) ->
      let (typs, typ) = open_type typ2 (n - 1) in
      (typ1 :: typs, typ)
    | _ -> failwith "Expected an arrow type."

(** The context to know if parenthesis are needed. *)
module Context = struct
  type t =
    | Apply
    | Arrow
    | Sum
    | Tuple

  let get_order (context : t) : int =
    match context with
    | Apply -> 0
    | Arrow -> 3
    | Sum -> 2
    | Tuple -> 1

  let should_parens (context : t option) (current_context : t) : bool =
    match context with
    | None -> false
    | Some context ->
      let order = get_order context in
      let current_order = get_order current_context in
      order <= current_order

  let parens
    (context : t option)
    (current_context : t)
    (doc : SmartPrint.t)
    : SmartPrint.t =
    Pp.parens (should_parens context current_context) doc
end

let rec accumulate_nested_arrows (typ : t) : t list * t =
  match typ with
  | Arrow (typ_x, typ_y) ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ_y in
    (typ_x :: typ_xs, typ_y)
  | _ -> ([], typ)

(** Pretty-print a type. Use the [context] parameter to know if we should add
    parenthesis. *)
let rec to_coq
  (subst : (Name.t -> Name.t) option)
  (context : Context.t option)
  (typ : t)
  : SmartPrint.t =
  match typ with
  | Variable x -> Name.to_coq x
  | Arrow _ ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ in
    Context.parens context Context.Arrow @@ group (
      separate space (typ_xs |> List.map (fun typ_x ->
        group (to_coq subst (Some Context.Arrow) typ_x ^^ !^ "->"
      ))) ^^
      to_coq subst (Some Context.Arrow) typ_y
    )
  | Sum typs ->
    let typs = typs |> List.map (fun (name, typ) ->
      let context = if List.length typs = 1 then context else Some Sum in
      group (nest (!^ "(*" ^^ !^ ("`" ^ name) ^^ !^ "*)") ^^ to_coq subst context typ)
    ) in
    begin match typs with
    | [] -> !^ "Empty_set"
    | [typ] -> typ
    | _ ->
      Context.parens context Context.Sum @@ nest @@
      separate (space ^^ !^ "+" ^^ space) typs
    end
  | Tuple typs ->
    begin match typs with
    | [] -> !^ "unit"
    | [typ] -> to_coq subst context typ
    | _ ->
      Context.parens context Context.Tuple @@ nest @@
      separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq subst (Some Context.Tuple)) typs)
    end
  | Apply (path, typs) ->
    let path =
      match subst with
      | None -> path
      | Some subst ->
        begin match path with
        | MixedPath.PathName { path = []; base = name } -> MixedPath.of_name (subst name)
        | _ -> path
        end in
    Pp.parens (Context.should_parens context Context.Apply && typs <> []) @@
    nest @@ separate space
      (MixedPath.to_coq path :: List.map (to_coq subst (Some Context.Apply)) typs)
  | Package (path_name, typ_params) ->
    let existential_typs =
      Tree.flatten typ_params |>
      List.filter (fun (_, typ) -> typ = None) |>
      List.map (fun (path_name, _) ->
        Name.to_coq (ModuleTypParams.get_typ_param_name path_name)
      ) in
    nest (braces (
      (match existential_typs with
      | [] -> !^ "_" ^^ !^ ":" ^^ !^ "unit"
      | [typ] -> typ ^^ !^ ":" ^^ !^ "_"
      | _ -> !^ "'" ^-^ OCaml.tuple existential_typs ^^ !^ ":" ^^ !^ "_"
      ) ^^ !^ "&" ^^
      nest (
        nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ^^
        separate space (Tree.flatten typ_params |> List.map (fun (path_name, typ) ->
          match typ with
          | None -> Name.to_coq (ModuleTypParams.get_typ_param_name path_name)
          | Some typ -> to_coq subst (Some Context.Apply) typ
        ))
      )
    ))
