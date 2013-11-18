(** Patterns used for the "match". *)
open Typedtree

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
  | Tpat_construct (path, _, _, ps, _) -> Constructor (PathName.of_path path, List.map of_pattern ps)
  | Tpat_alias (p, x, _) -> Alias (of_pattern p, Name.of_ident x)
  | Tpat_constant c -> Constant (Constant.of_constant c)
  | Tpat_record (fields, _) -> Record (List.map (fun (x, _, _, p) -> (PathName.of_path x, of_pattern p)) fields)
  | _ -> failwith "unhandled pattern"

(** Pretty-print a pattern (inside parenthesis if the [paren] flag is set). *)
let rec pp (f : Format.formatter) (paren : bool) (p : t) : unit =
  match p with
  | Any -> Format.fprintf f "_"
  | Constant c -> Constant.pp f c
  | Variable x -> Name.pp f x
  | Tuple ps ->
    Format.fprintf f "(";
    Pp.sep_by ps (fun _ -> Format.fprintf f ",@ ") (fun p -> pp f false p);
    Format.fprintf f ")"
  | Constructor (path, ps) ->
    if ps = [] then
      PathName.pp f path
    else (
      Pp.open_paren f paren;
      PathName.pp f path;
      Format.fprintf f "@ ";
      Pp.sep_by ps (fun _ -> Format.fprintf f "@ ") (fun p -> pp f true p);
      Pp.close_paren f paren)
  | Alias (p, x) ->
    Pp.open_paren f paren;
    pp f false p;
    Format.fprintf f "@ as@ ";
    Name.pp f x;
    Pp.close_paren f paren
  | Record fields ->
    Format.fprintf f "{|@ ";
    Pp.sep_by fields (fun _ -> Format.fprintf f ";@ ") (fun (x, p) ->
      PathName.pp f x;
      Format.fprintf f "@ :=@ ";
      pp f false p);
    Format.fprintf f "@ |}"