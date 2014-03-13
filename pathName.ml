(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open SmartPrint

type t = {
  path : Name.t list;
  base : Name.t }

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (x : t) : t =
  match x with
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = ["Pervasives"]; base = base } ->
    (match base with
    | "=" -> { path = []; base = "equiv_decb" }
    | "<>" -> { path = []; base = "nequiv_decb" }
    | "<=" -> { path = ["Z"]; base = "leb" }
    | ">=" -> { path = ["Z"]; base = "geb" }
    | "<" -> { path = ["Z"]; base = "ltb" }
    | ">" -> { path = ["Z"]; base = "gtb" }
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
    | "invalid_arg" -> { path = []; base = "invalid_arg" }
    | "failwith" -> { path = []; base = "failwith" }
    | "print_char" -> { path = []; base = "print_char" }
    | "print_string" -> { path = []; base = "print_string" }
    | "print_int" -> { path = []; base = "print_int" }
    | "print_endline" -> { path = []; base = "print_endline" }
    | "print_newline" -> { path = []; base = "print_newline" }
    | "prerr_char" -> { path = []; base = "prerr_char" }
    | "prerr_string" -> { path = []; base = "prerr_string" }
    | "prerr_int" -> { path = []; base = "prerr_int" }
    | "prerr_endline" -> { path = []; base = "prerr_endline" }
    | "prerr_newline" -> { path = []; base = "prerr_newline" }
    | "read_line" -> { path = []; base = "read_line" }
    | "read_int" -> { path = []; base = "read_int" }
    | _ -> x)
  | _ -> x

(** Pretty-print a global name. *)
let pp (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map (fun s -> !^ s) (x.path @ [x.base]))

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  convert { path = path; base = base }

(** Import an OCaml [Longident.t]. *)
let of_longident (longident : Longident.t) : t =
  match List.rev (Longident.flatten longident) with
  | [] -> failwith "Expected a non empty list."
  | x :: xs -> of_name xs x

(** Import an OCaml location. *)
let of_loc (loc : Longident.t loc) : t = 
  of_longident loc.txt

(** Import an OCaml [Path.t]. *)
let of_path (p : Path.t) : t =
  let rec aux p : Name.t list * Name.t =
    match p with
    | Path.Pident x -> ([], Name.of_ident x)
    | Path.Pdot (p, s, _) ->
      let (path, base) = aux p in
      (base :: path, s)
    | Path.Papply _ -> failwith "application of paths not handled" in
  let (path, base) = aux p in
  of_name (List.rev path) base