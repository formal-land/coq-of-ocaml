(** A type, with free type variables for polymorphic arguments. *)
open Types
open Sexplib.Std
open SmartPrint
open Monad.Notations

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of MixedPath.t * t list
  | Package of PathName.t * t option Tree.t
  [@@deriving sexp]

(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_type_expr
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * Name.Set.t) Monad.t =
  match typ.desc with
  | Tvar x ->
    (match x with
    | None ->
      if with_free_vars then
        let n = Name.Map.cardinal typ_vars in
        return (Printf.sprintf "A%d" typ.id, String.make 1 (Char.chr (Char.code 'A' + n)))
      else
        raise NotSupported "The placeholders `_` in types are not handled"
    | Some x -> return (x, x)) >>= fun (source_name, generated_name) ->
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
    of_type_expr with_free_vars typ_vars typ_x >>= fun (typ_x, typ_vars, new_typ_vars_x) ->
    of_type_expr with_free_vars typ_vars typ_y >>= fun (typ_y, typ_vars, new_typ_vars_y) ->
    return (Arrow (typ_x, typ_y), typ_vars, Name.Set.union new_typ_vars_x new_typ_vars_y)
  | Ttuple typs ->
    of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    return (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    of_typs_exprs with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    MixedPath.of_path path >>= fun mixed_path ->
    return (Apply (mixed_path, typs), typ_vars, new_typ_vars)
  | Tobject _ -> raise NotSupported "Object types are not handled"
  | Tfield _ -> raise NotSupported "Field types are not handled"
  | Tnil -> raise NotSupported "Nil type is not handled"
  | Tlink typ | Tsubst typ -> of_type_expr with_free_vars typ_vars typ
  | Tvariant _ -> raise NotSupported "Polymorphic variant types are not handled"
  | Tunivar _ | Tpoly (_, _ :: _) -> raise NotSupported "Forall quantifier is not handled (yet)"
  | Tpoly (typ, []) -> of_type_expr with_free_vars typ_vars typ
  | Tpackage (path, idents, typs) ->
      let path_name = PathName.of_path path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let path_name = PathName.of_long_ident ident in
          of_type_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
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
      return (Package (path_name, typ_params), typ_vars, Name.Set.empty)

and of_typs_exprs
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * Name.Set.t) Monad.t =
  (Monad.List.fold_left
    (fun (typs, typ_vars, new_typ_vars) typ ->
      of_type_expr with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
      return (typ :: typs, typ_vars, Name.Set.union new_typ_vars new_typ_vars')
    )
    ([], typ_vars, Name.Set.empty)
    typs
  ) >>= fun (typs, typ_vars, new_typ_vars) ->
  return (List.rev typs, typ_vars, new_typ_vars)

let of_type_expr_without_free_vars (typ : Types.type_expr) : t Monad.t =
  of_type_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
  return typ

let of_type_expr_variable (typ : Types.type_expr) : Name.t Monad.t =
  match typ.desc with
  | Tvar (Some x) -> return x
  | _ -> raise NotSupported "Only type variables are supported as parameters"

let rec typ_args (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
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

(** Pretty-print a type (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.to_coq x
  | Arrow (typ_x, typ_y) ->
    Pp.parens paren @@ nest (to_coq true typ_x ^^ !^ "->" ^^ to_coq false typ_y)
  | Tuple typs ->
    (match typs with
    | [] -> !^ "unit"
    | _ ->
      Pp.parens paren @@ nest @@ separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq true) typs))
  | Apply (path, typs) ->
    Pp.parens (paren && typs <> []) @@ nest @@ separate space
      (MixedPath.to_coq path :: List.map (to_coq true) typs)
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
        PathName.to_coq path_name ^^
        separate space (Tree.flatten typ_params |> List.map (fun (path_name, typ) ->
          match typ with
          | None -> Name.to_coq (ModuleTypParams.get_typ_param_name path_name)
          | Some typ -> to_coq true typ
        ))
      )
    ))
