(** Patterns used for the "match". *)
open Typedtree
open Types
open PPrint

type t =
  | Any
  | Constant of Constant.t
  | Variable of Name.t
  | Tuple of t list
  | Constructor of PathName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * Name.t
  | Record of (PathName.t * t) list (** A list of fields from a record with their expected patterns. *)

(** Import an OCaml pattern. *)
let rec of_pattern (p : pattern) : t =
  match p.pat_desc with
  | Tpat_any -> Any
  | Tpat_var (x, _) -> Variable (Name.of_ident x)
  | Tpat_tuple ps -> Tuple (List.map of_pattern ps)
  | Tpat_construct (x, _, ps) -> Constructor (PathName.of_loc x, List.map of_pattern ps)
  | Tpat_alias (p, x, _) -> Alias (of_pattern p, Name.of_ident x)
  | Tpat_constant c -> Constant (Constant.of_constant c)
  | Tpat_record (fields, _) -> Record (List.map (fun (x, _, p) -> (PathName.of_loc x, of_pattern p)) fields)
  | _ -> failwith "unhandled pattern"

(** Pretty-print a pattern (inside parenthesis if the [paren] flag is set). *)
let rec pp (paren : bool) (p : t) : document =
  match p with
  | Any -> !^ "_"
  | Constant c -> Constant.pp c
  | Variable x -> Name.pp x
  | Tuple ps -> group (lparen ^^ flow (!^ "," ^^ break 1) (List.map (pp false) ps) ^^ rparen)
  | Constructor (x, ps) ->
    if ps = [] then
      PathName.pp x
    else
      group (
        Pp.open_paren paren ^^
        flow (break 1) (PathName.pp x :: List.map (pp true) ps) ^^
        Pp.close_paren paren)
  | Alias (p, x) ->
    group (
      Pp.open_paren paren ^^
      flow (break 1) [pp false p; !^ "as"; Name.pp x] ^^
      Pp.close_paren paren)
  | Record fields ->
    group (flow (break 1) [
      !^ "{|";
      flow (!^ ";" ^^ break 1) (fields |> List.map (fun (x, p) ->
        group (flow (break 1) [PathName.pp x; !^ ":="; pp false p])));
      !^ "|}"])