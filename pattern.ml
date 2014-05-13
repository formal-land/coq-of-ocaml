(** Patterns used for the "match". *)
open Typedtree
open Types
open SmartPrint

type t =
  | Any
  | Constant of Constant.t
  | Variable of Name.t
  | Tuple of t list
  | Constructor of BoundName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * Name.t
  | Record of (BoundName.t * t) list (** A list of fields from a record with their expected patterns. *)
  | Or of t * t

let rec pp (p : t) : SmartPrint.t =
  match p with
  | Any -> !^ "Any"
  | Constant c -> Constant.pp c
  | Variable x -> Name.pp x
  | Tuple ps -> nest (!^ "Tuple" ^^ OCaml.tuple (List.map pp ps))
  | Constructor (x, ps) ->
    nest (!^ "Constructor" ^^ OCaml.tuple (BoundName.pp x :: List.map pp ps))
  | Alias (p, x) -> nest (!^ "Alias" ^^ OCaml.tuple [pp p; Name.pp x])
  | Record fields ->
    nest (!^ "Record" ^^ OCaml.tuple (fields |> List.map (fun (x, p) ->
      nest @@ parens (BoundName.pp x ^-^ !^ "," ^^ pp p))))
  | Or (p1, p2) -> nest (!^ "Or" ^^ OCaml.tuple [pp p1; pp p2])

(** Import an OCaml pattern. *)
let rec of_pattern (env : 'a FullEnvi.t) (p : pattern) : t =
  let l = Loc.of_location p.pat_loc in
  match p.pat_desc with
  | Tpat_any -> Any
  | Tpat_var (x, _) -> Variable (Name.of_ident x)
  | Tpat_tuple ps -> Tuple (List.map (of_pattern env) ps)
  | Tpat_construct (x, _, ps) ->
    let x = Envi.bound_name l (PathName.of_loc x) env.FullEnvi.constructors in
    Constructor (x, List.map (of_pattern env) ps)
  | Tpat_alias (p, x, _) -> Alias (of_pattern env p, Name.of_ident x)
  | Tpat_constant c -> Constant (Constant.of_constant l c)
  | Tpat_record (fields, _) ->
    Record (fields |> List.map (fun (x, _, p) ->
      let x = Envi.bound_name l (PathName.of_loc x) env.FullEnvi.fields in
      (x, of_pattern env p)))
  | Tpat_or (p1, p2, _) -> Or (of_pattern env p1, of_pattern env p2)
  | _ -> Error.raise l "Unhandled pattern."

(** Free variables in a pattern. *)
let rec free_variables (p : t) : Name.Set.t =
  let aux ps =
    List.fold_left (fun s p -> Name.Set.union s (free_variables p))
    Name.Set.empty ps in
  match p with
  | Any | Constant _ -> Name.Set.empty
  | Variable x -> Name.Set.singleton x
  | Tuple ps | Constructor (_, ps) -> aux ps
  | Alias (p, x) -> Name.Set.union (Name.Set.singleton x) (free_variables p)
  | Record fields -> aux (List.map snd fields)
  | Or (p1, p2) -> Name.Set.inter (free_variables p1) (free_variables p2)

let add_to_env (p : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  Name.Set.fold (fun x env -> FullEnvi.add_var [] x () env)
    (free_variables p) env

(** Pretty-print a pattern to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (p : t) : SmartPrint.t =
  match p with
  | Any -> !^ "_"
  | Constant c -> Constant.to_coq c
  | Variable x -> Name.to_coq x
  | Tuple ps ->
    if ps = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq false) ps)
  | Constructor (x, ps) ->
    if ps = [] then
      BoundName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (BoundName.to_coq x :: List.map (to_coq true) ps)
  | Alias (p, x) ->
    Pp.parens paren @@ nest (to_coq false p ^^ !^ "as" ^^ Name.to_coq x)
  | Record fields ->
    !^ "{|" ^^
    nest_all @@ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, p) ->
      nest (BoundName.to_coq x ^^ !^ ":=" ^^ to_coq false p)))
    ^^ !^ "|}"
  | Or (p1, p2) -> to_coq false p1 ^^ !^ "|" ^^ to_coq false p2