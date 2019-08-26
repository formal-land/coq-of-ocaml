(** Patterns used for the "match". *)
open Typedtree
open Types
open Sexplib.Std
open SmartPrint

type t =
  | Any
  | Constant of Constant.t
  | Variable of Name.t
  | Tuple of t list
  | Constructor of PathName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * Name.t
  | Record of (PathName.t * t) list (** A list of fields from a record with their expected patterns. *)
  | Or of t * t
  [@@deriving sexp]

(** Import an OCaml pattern. *)
let rec of_pattern (p : pattern) : t =
  let l = Loc.of_location p.pat_loc in
  match p.pat_desc with
  | Tpat_any -> Any
  | Tpat_var (x, _) -> Variable (Name.of_ident x)
  | Tpat_tuple ps -> Tuple (List.map of_pattern ps)
  | Tpat_construct (x, _, ps) ->
    let x = PathName.of_loc x in
    Constructor (x, List.map of_pattern ps)
  | Tpat_alias (p, x, _) -> Alias (of_pattern p, Name.of_ident x)
  | Tpat_constant c -> Constant (Constant.of_constant l c)
  | Tpat_record (fields, _) ->
    Record (fields |> List.map (fun (x, _, p) ->
      let x = PathName.of_loc x in
      (x, of_pattern p)
    ))
  | Tpat_or (p1, p2, _) -> Or (of_pattern p1, of_pattern p2)
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
      PathName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (PathName.to_coq x :: List.map (to_coq true) ps)
  | Alias (p, x) ->
    Pp.parens paren @@ nest (to_coq false p ^^ !^ "as" ^^ Name.to_coq x)
  | Record fields ->
    !^ "{|" ^^
    nest_all @@ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, p) ->
      nest (PathName.to_coq x ^^ !^ ":=" ^^ to_coq false p)))
    ^^ !^ "|}"
  | Or (p1, p2) -> to_coq false p1 ^^ !^ "|" ^^ to_coq false p2
