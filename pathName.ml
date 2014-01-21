(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open SmartPrint

module Path' = Path

module Path = struct
  type t = string list
end

type t = {
  path : Path.t;
  base : Name.t}

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (p : t) : t =
  match p with
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = ["Pervasives"]; base = x } ->
    (match x with
    | "=" -> { path = []; base = "equiv_decb" }
    | "<>" -> { path = []; base = "nequiv_decb" }
    | "<" -> { path = ["Z"]; base = "ltb" }
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
    | _ -> p)
  | _ -> p

(** Pretty-print a global name. *)
let pp (x : t) : SmartPrint.t =
  single_quotes @@ separate (!^ ".") (List.map (fun s -> !^ s) (x.path @ [x.base]))

(** Lift a local name to a global name. *)
let of_name (path : Path.t) (x : Name.t) : t =
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
let of_path (p : Path'.t) : t =
  let rec aux p =
    match p with
    | Path'.Pident x -> { path = []; base = Name.of_ident x }
    | Path'.Pdot (p, s, _) ->
      let p = aux p in
      { path = p.base :: p.path; base = s }
    | Path'.Papply _ -> failwith "application of paths not handled" in
  let p = aux p in
  convert { path = List.rev p.path; base = p.base }

let fresh (prefix : string) (v : 'a) (env : 'a Map.t) : Name.t * 'a Map.t =
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if Map.mem (of_name [] @@ prefix_n prefix n) env then
      first_n (n + 1)
    else
      n in
  let x = prefix_n prefix (first_n 0) in
  (x, Map.add (of_name [] x) v env)

(** Pretty-print a global name to Coq. *)
let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))