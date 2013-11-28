(** A type, with free type variables for polymorphic arguments. *)
open Types
open PPrint

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of PathName.t * t list
  | Monad of t

(** Import an OCaml type. *)
let rec of_type_expr (typ : Types.type_expr) : t =
  match typ.desc with
  | Tvar None -> Variable (Printf.sprintf "A%d" typ.id)
  | Tvar (Some x) -> Variable x
  | Tarrow (_, typ_x, typ_y, _) -> Arrow (of_type_expr typ_x, of_type_expr typ_y)
  | Ttuple typs -> Tuple (List.map of_type_expr typs)
  | Tconstr (path, typs, _) -> Apply (PathName.of_path path, List.map of_type_expr typs)
  | Tlink typ -> of_type_expr typ
  | Tpoly (typ, []) -> of_type_expr typ
  | _ -> failwith "type not handled"

(** The set of free variables in a type (the polymorphic arguments). *)
let rec free_vars (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ_x, typ_y) -> Name.Set.union (free_vars typ_x) (free_vars typ_y)
  | Tuple typs | Apply (_, typs) -> List.fold_left (fun s typ -> Name.Set.union s (free_vars typ)) Name.Set.empty typs
  | Monad typ -> free_vars typ

(** In a function's type, extract the list of arguments' types (up to [n] elements) and the body's type.  *)
let rec open_function (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ_x, typ_y) ->
      let (typs, typ) = open_function typ_y (n - 1) in
      (typ_x :: typs, typ)
    | _ -> ([], typ)

(** Replace a variable name by another. *)
let rec substitute_variable (typ : t) (x : Name.t) (x' : Name.t) : t =
  match typ with
  | Variable y -> if x = y then Variable x' else typ
  | Arrow (typ1, typ2) -> Arrow (substitute_variable typ1 x x', substitute_variable typ2 x x')
  | Tuple typs -> Tuple (List.map (fun typ -> substitute_variable typ x x') typs)
  | Apply (path, typs) -> Apply (path, List.map (fun typ -> substitute_variable typ x x') typs)
  | Monad typ -> Monad (substitute_variable typ x x')

(** The monadic transformation of the type [typ]. *)
let rec monadise (typ : t) : t =
  match typ with
  | Variable _ -> typ
  | Arrow (typ_x, typ_y) -> Arrow (monadise typ_x, Monad (monadise typ_y))
  | Tuple typs -> Tuple (List.map monadise typs)
  | Apply (path, typs) -> Apply (path, List.map monadise typs)
  | Monad _ -> failwith "This type is already monadic."

(** Pretty-print a type (inside parenthesis if the [paren] flag is set). *)
let rec pp (paren : bool) (typ : t) : document =
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ_x, typ_y) ->
    group (
      Pp.open_paren paren ^^
      flow (break 1) [pp true typ_x; !^ "->"; pp false typ_y] ^^
      Pp.close_paren paren)
  | Tuple typs ->
    (match typs with
    | [] -> !^ "unit"
    | _ ->
      group (
        Pp.open_paren paren ^^
        flow (break 1 ^^ !^ "*" ^^ break 1) (List.map (pp true) typs) ^^
        Pp.close_paren paren))
  | Apply (path, typs) ->
    group (
      Pp.open_paren (paren && typs <> []) ^^
      flow (break 1) (PathName.pp path :: List.map (pp true) typs) ^^
      Pp.close_paren (paren && typs <> []))
  | Monad typ -> pp paren (Apply (PathName.of_name [] "M", [typ]))
