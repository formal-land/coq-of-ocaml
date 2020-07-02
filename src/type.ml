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
  | Package of bool * PathName.t * arity_or_typ Tree.t
  | ForallModule of Name.t * t * t
  | ForallTyps of Name.t list * t
  | FunTyps of Name.t list * t
  | Error of string
and arity_or_typ =
  | Arity of int
  | Typ of t


let to_string : t -> string = function
  | Variable _ -> "Var"
  | Arrow _ -> "Arrow"
  | Sum _ -> "Sum"
  | Tuple _ -> "Tuple"
  | Apply (mpath, _) -> MixedPath.to_string mpath
  | Package _ -> "Package"
  | ForallModule _ -> "ForallModule"
  | ForallTyps _ -> "ForallTyps"
  | FunTyps _ -> "FunTyps"
  | Error s -> "Error" ^ s

let equal (t1 : t) (t2 : t): bool =
  match t1, t2 with
  | Variable _ , Variable _ -> true
  | Arrow _, Arrow _ -> true
  | Sum _, Sum _ -> true
  | Tuple _, Tuple _ -> true
  | Apply (s1, _), Apply (s2, _) -> s1 = s2
  | Package _, Package _ -> true
  | ForallModule _, ForallModule _ -> true
  | ForallTyps _, ForallTyps _ -> true
  | FunTyps _, FunTyps _ -> true
  | Error _, Error _ -> true
  | _ -> false

let compare t1 t2 : int =
  if equal t1 t2
  then 0
  else 1

let type_exprs_of_row_field (row_field : Types.row_field)
  : Types.type_expr list =
  match row_field with
  | Rpresent None -> []
  | Rpresent (Some typ) -> [typ]
  | Reither (_, typs, _, _) -> typs
  | Rabsent -> []

let filter_typ_params_in_valid_set
  (typ_params : AdtParameters.AdtVariable.t list) (valid_set : Name.Set.t) : bool list =
  typ_params |> List.map (function
      | AdtParameters.AdtVariable.Parameter name -> Name.Set.mem name valid_set
      | _ -> false )

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
    let* source_name = Name.of_string false source_name in
    let* generated_name = Name.of_string false generated_name in
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
  | Tobject (_, object_descr) ->
    begin match !object_descr with
    | Some (path, _ :: typs) ->
      of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
      MixedPath.of_path false path None >>= fun mixed_path ->
      return (Apply (mixed_path, typs), typ_vars, new_typ_vars)
    | _ ->
      raise
        (Error "unhandled_object_type", typ_vars, Name.Set.empty)
        NotSupported
        "We do not handle this form of object types"
    end
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
      (Error "nil", typ_vars, Name.Set.empty)
      NotSupported
      "Nil type is not handled"
  | Tlink typ | Tsubst typ -> of_typ_expr with_free_vars typ_vars typ
  | Tvariant { row_fields; _ } ->
    PathName.typ_of_variants (List.map fst row_fields) >>= fun path_name ->
    begin match path_name with
    | Some path_name ->
      return (
        Apply (MixedPath.PathName path_name, []),
        typ_vars,
        Name.Set.empty
      )
    | None ->
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
      return (Sum (List.rev fields), typ_vars, new_typ_vars)
    end
  | Tpoly (typ, typ_args) ->
    let* typ_args =
      AdtParameters.typ_params_ghost_marked typ_args in
    let typ_args = typ_args |> AdtParameters.get_parameters in
    of_typ_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars_typ) ->
    return (ForallTyps (typ_args, typ), typ_vars, new_typ_vars_typ)
  | Tpackage (path, idents, typs) ->
      let* path_name = PathName.of_path_without_convert false path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let* path_name = PathName.of_long_ident false ident in
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
      ModuleTypParams.get_module_typ_declaration_typ_params_arity
        module_typ >>= fun signature_typ_params ->
      let typ_params = List.fold_left
        (fun typ_values (path_name, typ) ->
          Tree.map_at typ_values path_name (fun _ -> Typ typ)
        )
        (signature_typ_params |> Tree.map (fun arity -> Arity arity))
        typ_substitutions in
      return (Package (true, path_name, typ_params), typ_vars, new_typ_vars)

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

let rec of_type_expr_variable (typ : Types.type_expr) : Name.t Monad.t =
  match typ.desc with
  | Tvar (Some x) | Tunivar (Some x) -> Name.of_string false x
  | Tlink typ | Tsubst typ -> of_type_expr_variable typ
  | _ ->
    raise
      (Name.of_string_raw "expected_variable")
      NotSupported
      "Only type variables are supported as parameters."

let of_type_expr_without_free_vars (typ : Types.type_expr) : t Monad.t =
  of_typ_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
  return typ

(** We do not generate error messages for this function. Indeed, if there are
    errors for the following types, they should be noticed elsewhere (by the
    conversion function to Coq for example). *)
let rec existential_typs_of_typ (typ : Types.type_expr) : Name.Set.t Monad.t =
  match typ.desc with
  | Tvar _ | Tunivar _ -> return Name.Set.empty
  | Tarrow (_, typ_x, typ_y, _) -> existential_typs_of_typs [typ_x; typ_y]
  | Ttuple typs -> existential_typs_of_typs typs
  | Tconstr (path, typs, _) ->
    get_env >>= fun env ->
    let* path_existential =
      match path with
      | Path.Pident ident ->
        begin match Env.find_type path env with
        | _ -> return Name.Set.empty
        | exception Not_found ->
          let* ident = Name.of_ident false ident in
          return (Name.Set.singleton ident)
        end
      | _ -> return Name.Set.empty in
    existential_typs_of_typs typs >>= fun existentials ->
    return (Name.Set.union path_existential existentials)
  | Tobject (_, object_descr) ->
    let param_typs =
      match !object_descr with
      | Some (_, _ :: param_typs) -> List.tl param_typs
      | _ -> [] in
    existential_typs_of_typs param_typs
  | Tfield (_, _, typ1, typ2) -> existential_typs_of_typs [typ1; typ2]
  | Tnil -> return Name.Set.empty
  | Tlink typ | Tsubst typ -> existential_typs_of_typ typ
  | Tvariant { row_fields; _ } ->
    existential_typs_of_typs (
      row_fields |>
      List.map (fun (_, row_field) -> type_exprs_of_row_field row_field) |>
      List.concat
    )
  | Tpoly (typ, typs) -> existential_typs_of_typs (typ :: typs)
  | Tpackage (_, _, typs) -> existential_typs_of_typs typs

and existential_typs_of_typs (typs : Types.type_expr list)
  : Name.Set.t Monad.t =
  Monad.List.fold_left
    (fun existentials typ ->
      existential_typs_of_typ typ >>= fun existentials_typ ->
      return (Name.Set.union existentials existentials_typ)
    )
    Name.Set.empty typs

(** The free variables of a type. *)
let rec typ_args_of_typ (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Sum typs -> typ_args_of_typs (List.map snd typs)
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (typ_args_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    Name.Set.union (typ_args_of_typ param) (typ_args_of_typ result)
  | ForallTyps (typ_params, typ) | FunTyps (typ_params, typ) ->
    Name.Set.diff (typ_args_of_typ typ) (Name.Set.of_list typ_params)
  | Error _ -> Name.Set.empty

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args_of_typ typ))
    Name.Set.empty typs

(** The local type constructors of a type. Used to detect the existential
    variables which are actually used by a type, once we remove the phantom
    types. *)
let rec local_typ_constructors_of_typ (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> local_typ_constructors_of_typs [typ1; typ2]
  | Sum typs -> local_typ_constructors_of_typs (List.map snd typs)
  | Tuple typs -> local_typ_constructors_of_typs typs
  | Apply (mixed_path, typs) ->
    let local_typ_constructors = local_typ_constructors_of_typs typs in
    begin match mixed_path with
    | MixedPath.PathName { path = []; base } ->
      Name.Set.add base local_typ_constructors
    | _ -> local_typ_constructors
    end
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (local_typ_constructors_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    local_typ_constructors_of_typs [param; result]
  | ForallTyps (_, typ) | FunTyps (_, typ) -> local_typ_constructors_of_typ typ
  | Error _ -> Name.Set.empty

and local_typ_constructors_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (local_typ_constructors_of_typ typ))
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
    | Forall

  let get_order (context : t) : int =
    match context with
    | Apply -> 0
    | Arrow -> 3
    | Sum -> 2
    | Tuple -> 1
    | Forall -> 4

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

module Subst = struct
  type t = {
    name : Name.t -> Name.t;
    path_name : PathName.t -> PathName.t }
end

(** Pretty-print a type. Use the [context] parameter to know if we should add
    parenthesis. *)
let rec to_coq (subst : Subst.t option) (context : Context.t option) (typ : t)
  : SmartPrint.t =
  match typ with
  | Variable x ->
    let x =
      match subst with
      | None -> x
      | Some subst -> subst.name x in
    Name.to_coq x
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
        | MixedPath.PathName path_name ->
          MixedPath.PathName (subst.path_name path_name)
        | _ -> path
        end in
    Pp.parens (Context.should_parens context Context.Apply && typs <> []) @@
    nest @@ separate space
      (MixedPath.to_coq path :: List.map (to_coq subst (Some Context.Apply)) typs)
  | Package (is_in_exp, path_name, typ_params) ->
    let existential_typs =
      Tree.flatten typ_params |>
      Util.List.filter_map (function
        | (path_name, Arity arity) -> Some (path_name, arity)
        | _ -> None
      ) in
    let existential_typs_pattern =
      existential_typs |>
      List.map (fun (path_name, _) ->
        ModuleTypParams.to_coq_typ_param_name path_name
      ) |>
      Pp.primitive_tuple_pattern in
    let existential_typs_typ =
      existential_typs |>
      List.map (fun (_, arity) -> Pp.typ_arity arity) |>
      Pp.primitive_tuple_type in
    nest (braces (
      existential_typs_pattern ^^ !^ ":" ^^ existential_typs_typ ^^
      (if is_in_exp then !^ "@" else !^ "&") ^^
      nest (
        separate space (
          nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ::
          (Tree.flatten typ_params |> List.map (fun (path_name, typ) ->
            let name = ModuleTypParams.to_coq_typ_param_name path_name in
            nest (parens (
              name ^^ !^ ":=" ^^
              match typ with
              | Arity _ -> name
              | Typ typ -> to_coq subst (Some Context.Apply) typ
            ))
          ))
        )
      )
    ))
  | ForallModule (name, param, result) ->
    Context.parens context Context.Forall @@ nest (
      !^ "forall" ^^ parens (
        Name.to_coq name ^^ !^ ":" ^^ to_coq subst None param
      ) ^-^ !^ "," ^^
      to_coq subst (Some Context.Forall) result
    )
  | ForallTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "forall" ^^ braces (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^-^ !^ "," ^^
        to_coq subst (Some Context.Forall) typ
      )
    end
  | FunTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "fun" ^^ parens (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^^ !^ "=>" ^^
        to_coq subst (Some Context.Forall) typ
      )
    end
  | Error message -> !^ message
