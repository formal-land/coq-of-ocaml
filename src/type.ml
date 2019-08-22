(** A type, with free type variables for polymorphic arguments. *)
open Types
open Sexplib.Std
open SmartPrint

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of BoundName.t * t list
  [@@deriving sexp]

(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_type_expr_new_typ_vars (env : FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (typ : Types.type_expr)
  : t * Name.t Name.Map.t * Name.Set.t =
  match typ.desc with
  | Tvar None ->
    let x = Printf.sprintf "A%d" typ.id in
    let (typ_vars, new_typ_vars, name) =
      if Name.Map.mem x typ_vars then (
        let name = Name.Map.find x typ_vars in
        (typ_vars, Name.Set.empty, name)
      ) else (
        let n = Name.Map.cardinal typ_vars in
        let name = String.make 1 (Char.chr (Char.code 'A' + n)) in
        let typ_vars = Name.Map.add x name typ_vars in
        (typ_vars, Name.Set.singleton name, name)) in
    let typ = Variable name in
    (typ, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    let (typ_x, typ_vars, new_typ_vars_x) = of_type_expr_new_typ_vars env loc typ_vars typ_x in
    let (typ_y, typ_vars, new_typ_vars_y) = of_type_expr_new_typ_vars env loc typ_vars typ_y in
    (Arrow (typ_x, typ_y), typ_vars, Name.Set.union new_typ_vars_x new_typ_vars_y)
  | Ttuple typs ->
    let (typs, typ_vars, new_typ_vars) = of_typs_exprs_new_free_vars env loc typ_vars typs in
    (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    let (typs, typ_vars, new_typ_vars) = of_typs_exprs_new_free_vars env loc typ_vars typs in
    let (x, ()) = Envi.bound_name loc (PathName.of_path loc path) env.FullEnvi.typs in
    (Apply (x, typs), typ_vars, new_typ_vars)
  | Tlink typ -> of_type_expr_new_typ_vars env loc typ_vars typ
  | Tpoly (typ, []) -> of_type_expr_new_typ_vars env loc typ_vars typ
  | _ ->
    Error.warn loc "Type not handled.";
    (Variable "unhandled_type", typ_vars, Name.Set.empty)

and of_typs_exprs_new_free_vars (env : FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (typs : Types.type_expr list)
  : t list * Name.t Name.Map.t * Name.Set.t =
  let (typs, typ_vars, new_typ_vars) =
    List.fold_left (fun (typs, typ_vars, new_typ_vars) typ ->
      let (typ, typ_vars, new_typ_vars') = of_type_expr_new_typ_vars env loc typ_vars typ in
      (typ :: typs, typ_vars, Name.Set.union new_typ_vars new_typ_vars'))
      ([], typ_vars, Name.Set.empty) typs in
  (List.rev typs, typ_vars, new_typ_vars)

let rec of_type_expr (env : FullEnvi.t) (loc : Loc.t) (typ : Types.type_expr) : t =
  match typ.desc with
  | Tvar None ->
    Error.raise loc "The placeholders `_` in types are not handled."
  | Tvar (Some x) -> Variable x
  | Tarrow (_, typ_x, typ_y, _) ->
    Arrow (of_type_expr env loc typ_x, of_type_expr env loc typ_y)
  | Ttuple typs ->
    Tuple (List.map (of_type_expr env loc) typs)
  | Tconstr (path, typs, _) ->
    let (x, ()) = Envi.bound_name loc (PathName.of_path loc path) env.FullEnvi.typs in
    Apply (x, List.map (of_type_expr env loc) typs)
  | Tlink typ -> of_type_expr env loc typ
  | Tpoly (typ, []) -> of_type_expr env loc typ
  | _ ->
    Error.warn loc "Type not handled.";
    Variable "unhandled_type"

let of_type_expr_variable (loc : Loc.t) (typ : Types.type_expr) : Name.t =
  match typ.desc with
  | Tvar (Some x) -> x
  | _ ->
    Error.warn loc "The type parameter was expected to be a variable.";
    "expected_a_type_variable"

let rec typ_args (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Tuple typs | Apply (_, typs) -> typ_args_of_typs typs

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
      (BoundName.to_coq path :: List.map (to_coq true) typs)
