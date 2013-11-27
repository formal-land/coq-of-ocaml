(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open PPrint

type t = {
  path : Name.t list;
  base : Name.t}

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (p : t) : t =
  match p with
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = ["Pervasives"]; base = x } -> (match x with
    | "=" -> { path = []; base = "equiv_decb" }
    | "<>" -> { path = []; base = "nequiv_decb" }
    | "not" -> { path = []; base = "negb" }
    | "&&" -> { path = []; base = "andb" }
    | "&" -> failwith "\"&\" is deprecated. Use \"&&\" instead."
    | "||" -> { path = []; base = "orb" }
    | "or" -> failwith "\"or\" is deprecated. Use \"||\" instead."
    | "|>" -> { path = []; base = "reverse_apply" }
    | "@@" -> { path = []; base = "apply" }
    | "~-" -> { path = ["Z"]; base = "opp" }
    | "~+" -> { path = []; base = "" }
    | "succ" -> { path = ["Z"]; base = "succ" }
    | "pred" -> { path = ["Z"]; base = "pred" }
    | "+" -> { path = ["Z"]; base = "add" }
    | "-" -> { path = ["Z"]; base = "sub" }
    | "*" -> { path = ["Z"]; base = "mul" }
    | "/" -> { path = ["Z"]; base = "div" }
    | "mod" -> { path = ["Z"]; base = "modulo" }
    | "abs" -> { path = ["Z"]; base = "abs" }
    | "land" -> { path = ["Z"]; base = "land" }
    | "lor" -> { path = ["Z"]; base = "lor" }
    | "lxor" -> { path = ["Z"]; base = "lxor" }
    | "lnot" -> failwith "\"lnot\" not handled."
    | "asr" -> failwith "\"asr\" not handled."
    | "lsl" -> { path = ["Z"]; base = "shiftl" }
    | "lsr" -> { path = ["Z"]; base = "shiftr" }
    | "^" -> { path = []; base = "append" }
    | "int_of_char" -> { path = []; base = "int_of_char" }
    | "char_of_int" -> { path = []; base = "char_of_int" }
    | "ignore" -> { path = []; base = "ignore" }
    | "string_of_bool" -> failwith "string_of_bool not handled."
    | "bool_of_string" -> failwith "bool_of_string not handled."
    | "string_of_int" -> failwith "string_of_int not handled."
    | "int_of_string" -> failwith "int_of_string not handled."
    | "fst" -> { path = []; base = "fst" }
    | "snd" -> { path = []; base = "snd" }
    | "@" -> { path = []; base = "app" }
    | _ -> p)
  | _ -> p

(** Lift a local name to a global name. *)
let of_name (path : string list) (x : Name.t) : t =
  convert { path = path; base = x }

(** Import an OCaml [Longident.t]. *)
let of_longident (longident : Longident.t) : t =
  match List.rev (Longident.flatten longident) with
  | [] -> assert false
  | x :: xs -> convert { path = xs; base = x }

(** Import an OCaml location. *)
let of_loc (loc : Longident.t loc) : t = 
  of_longident loc.txt

(** Import an OCaml [Path.t]. *)
let of_path (p : Path.t) : t =
  let rec aux p =
    match p with
    | Path.Pident x -> { path = []; base = Name.of_ident x }
    | Path.Pdot (p, s, _) ->
      let p = aux p in
      { path = p.base :: p.path; base = s }
    | Path.Papply _ -> failwith "application of paths not handled" in
  let p = aux p in
  convert { path = List.rev p.path; base = p.base }

(** Pretty-print a global name. *)
let pp (i : t) : document =
  separate (!^ ".") (List.map Name.pp (i.path @ [i.base]))