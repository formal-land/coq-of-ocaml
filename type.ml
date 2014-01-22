(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of PathName.t * t list
  | Monad of Effect.Descriptor.t * t

let rec pp (typ : t) : SmartPrint.t =
  match typ with
  | Variable x -> Name.pp x
  | Arrow (typ1, typ2) -> nest @@ parens (pp typ1 ^^ !^ "->" ^^ pp typ2)
  | Tuple typs -> nest @@ parens (separate (space ^^ !^ "*" ^^ space) (List.map pp typs))
  | Apply (x, typs) ->
    nest (!^ "Type" ^^ nest (parens (
      separate (!^ "," ^^ space) (PathName.pp x :: List.map pp typs))))
  | Monad (d, typ) -> nest (!^ "Monad" ^^ Pp.list [
    Effect.Descriptor.pp d; pp typ])

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
  | Tuple typs | Apply (_, typs) ->
    List.fold_left (fun s typ -> Name.Set.union s (free_vars typ)) Name.Set.empty typs
  | Monad (_, typ) -> free_vars typ

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

(** Replace a variable name by another. *)
let rec substitute_variable (typ : t) (x : Name.t) (x' : Name.t) : t =
  match typ with
  | Variable y -> if x = y then Variable x' else typ
  | Arrow (typ1, typ2) -> Arrow (substitute_variable typ1 x x', substitute_variable typ2 x x')
  | Tuple typs -> Tuple (List.map (fun typ -> substitute_variable typ x x') typs)
  | Apply (path, typs) -> Apply (path, List.map (fun typ -> substitute_variable typ x x') typs)
  | Monad (d, typ) -> Monad (d, substitute_variable typ x x')

let monadise (typ : t) (effect : Effect.t) : t =
  let rec aux (typ : t) (effect_typ : Effect.Type.t) : t =
    match (typ, effect_typ) with
    | (Variable _, Effect.Type.Pure) | (Tuple _, Effect.Type.Pure)
      | (Apply _, Effect.Type.Pure) | (Arrow _, Effect.Type.Pure) -> typ
    | (Arrow (typ1, typ2), Effect.Type.Arrow (d, effect_typ2)) ->
      let typ2 = aux typ2 effect_typ2 in
      Arrow (typ1,
        if Effect.Descriptor.is_pure d then
          typ2
        else
          Monad (d, typ2))
    | (Monad _, _) -> failwith "This type is already monadic."
    | _ -> failwith "Type and effect type are not compatible." in
  let typ = aux typ effect.typ in
  if Effect.Descriptor.is_pure effect.Effect.descriptor then
    typ
  else
    Monad (effect.Effect.descriptor, typ)

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
      (PathName.to_coq path :: List.map (to_coq true) typs)
  | Monad (d, typ) -> (* TODO; display [d] *)
    to_coq paren (Apply (PathName.of_name [] "M", [typ]))
