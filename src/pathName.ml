(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open Sexplib.Std
open SmartPrint

type t = {
  path : Name.t list;
  base : Name.t }
  [@@deriving sexp]

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (x : t) : t =
  match x with
  (* The core library *)
  (* Built-in types *)
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "bytes" } -> { path = []; base = "string" }
  | { path = []; base = "string" } -> { path = []; base = "string" }
  | { path = []; base = "bool" } -> { path = []; base = "bool" }
  | { path = []; base = "false" } -> { path = []; base = "false" }
  | { path = []; base = "true" } -> { path = []; base = "true" }
  | { path = []; base = "unit" } -> { path = []; base = "unit" }
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "list" } -> { path = []; base = "list" }
  | { path = []; base = "[]" } -> { path = []; base = "[]" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = []; base = "option" } -> { path = []; base = "option" }
  | { path = []; base = "None" } -> { path = []; base = "None" }
  | { path = []; base = "Some" } -> { path = []; base = "Some" }
  (* Predefined exceptions *)
  | { path = []; base = "Match_failure" } -> { path = ["OCaml"]; base = "Match_failure" }
  | { path = []; base = "Assert_failure" } -> { path = ["OCaml"]; base = "Assert_failure" }
  | { path = []; base = "Invalid_argument" } -> { path = ["OCaml"]; base = "Invalid_argument" }
  | { path = []; base = "Failure" } -> { path = ["OCaml"]; base = "Failure" }
  | { path = []; base = "Not_found" } -> { path = ["OCaml"]; base = "Not_found" }
  | { path = []; base = "Out_of_memory" } -> { path = ["OCaml"]; base = "Out_of_memory" }
  | { path = []; base = "Stack_overflow" } -> { path = ["OCaml"]; base = "Stack_overflow" }
  | { path = []; base = "Sys_error" } -> { path = ["OCaml"]; base = "Sys_error" }
  | { path = []; base = "End_of_file" } -> { path = ["OCaml"]; base = "End_of_file" }
  | { path = []; base = "Division_by_zero" } -> { path = ["OCaml"]; base = "Division_by_zero" }
  | { path = []; base = "Sys_blocked_io" } -> { path = ["OCaml"]; base = "Sys_blocked_io" }
  | { path = []; base = "Undefined_recursive_module" } -> { path = ["OCaml"]; base = "Undefined_recursive_module" }

  (* Stdlib *)
  (* Exceptions *)
  | { path = ["Stdlib"]; base = "invalid_arg" } -> { path = ["OCaml"; "Stdlib"]; base = "invalid_arg" }
  | { path = ["Stdlib"]; base = "failwith" } -> { path = ["OCaml"; "Stdlib"]; base = "failwith" }
  | { path = []; base = "Exit" } | { path = ["Stdlib"]; base = "Exit" } ->
    { path = ["OCaml"; "Stdlib"]; base = "Exit" }
  (* Comparisons *)
  | { path = ["Stdlib"]; base = "=" } -> { path = []; base = "equiv_decb" }
  | { path = ["Stdlib"]; base = "<>" } -> { path = []; base = "nequiv_decb" }
  | { path = ["Stdlib"]; base = "<" } -> { path = ["OCaml"; "Stdlib"]; base = "lt" }
  | { path = ["Stdlib"]; base = ">" } -> { path = ["OCaml"; "Stdlib"]; base = "gt" }
  | { path = ["Stdlib"]; base = "<=" } -> { path = ["OCaml"; "Stdlib"]; base = "le" }
  | { path = ["Stdlib"]; base = ">=" } -> { path = ["OCaml"; "Stdlib"]; base = "ge" }
  | { path = ["Stdlib"]; base = "compare" } -> { path = ["OCaml"; "Stdlib"]; base = "compare" }
  | { path = ["Stdlib"]; base = "min" } -> { path = ["OCaml"; "Stdlib"]; base = "min" }
  | { path = ["Stdlib"]; base = "max" } -> { path = ["OCaml"; "Stdlib"]; base = "max" }
  (* Boolean operations *)
  | { path = ["Stdlib"]; base = "not" } -> { path = []; base = "negb" }
  | { path = ["Stdlib"]; base = "&&" } -> { path = []; base = "andb" }
  | { path = ["Stdlib"]; base = "&" } -> { path = []; base = "andb" }
  | { path = ["Stdlib"]; base = "||" } -> { path = []; base = "orb" }
  | { path = ["Stdlib"]; base = "or" } -> { path = []; base = "orb" }
  (* Composition operators *)
  | { path = ["Stdlib"]; base = "|>" } -> { path = ["OCaml"; "Stdlib"]; base = "reverse_apply" }
  | { path = ["Stdlib"]; base = "@@" } -> { path = []; base = "apply" }
  (* Integer arithmetic *)
  | { path = ["Stdlib"]; base = "~-" } -> { path = ["Z"]; base = "opp" }
  | { path = ["Stdlib"]; base = "~+" } -> { path = []; base = "" }
  | { path = ["Stdlib"]; base = "succ" } -> { path = ["Z"]; base = "succ" }
  | { path = ["Stdlib"]; base = "pred" } -> { path = ["Z"]; base = "pred" }
  | { path = ["Stdlib"]; base = "+" } -> { path = ["Z"]; base = "add" }
  | { path = ["Stdlib"]; base = "-" } -> { path = ["Z"]; base = "sub" }
  | { path = ["Stdlib"]; base = "*" } -> { path = ["Z"]; base = "mul" }
  | { path = ["Stdlib"]; base = "/" } -> { path = ["Z"]; base = "div" }
  | { path = ["Stdlib"]; base = "mod" } -> { path = ["Z"]; base = "modulo" }
  | { path = ["Stdlib"]; base = "abs" } -> { path = ["Z"]; base = "abs" }
  (* Bitwise operations *)
  | { path = ["Stdlib"]; base = "land" } -> { path = ["Z"]; base = "land" }
  | { path = ["Stdlib"]; base = "lor" } -> { path = ["Z"]; base = "lor" }
  | { path = ["Stdlib"]; base = "lxor" } -> { path = ["Z"]; base = "lxor" }
  | { path = ["Stdlib"]; base = "lsl" } -> { path = ["Z"]; base = "shiftl" }
  | { path = ["Stdlib"]; base = "lsr" } -> { path = ["Z"]; base = "shiftr" }
  (* Floating-point arithmetic *)
  (* String operations *)
  | { path = ["Stdlib"]; base = "^" } -> { path = ["String"]; base = "append" }
  (* Character operations *)
  | { path = ["Stdlib"]; base = "int_of_char" } -> { path = ["OCaml"; "Stdlib"]; base = "int_of_char" }
  | { path = ["Stdlib"]; base = "char_of_int" } -> { path = ["OCaml"; "Stdlib"]; base = "char_of_int" }
  (* Unit operations *)
  | { path = ["Stdlib"]; base = "ignore" } -> { path = ["OCaml"; "Stdlib"]; base = "ignore" }
  (* String conversion functions *)
  | { path = ["Stdlib"]; base = "string_of_bool" } -> { path = ["OCaml"; "Stdlib"]; base = "string_of_bool" }
  | { path = ["Stdlib"]; base = "bool_of_string" } -> { path = ["OCaml"; "Stdlib"]; base = "bool_of_string" }
  | { path = ["Stdlib"]; base = "string_of_int" } -> { path = ["OCaml"; "Stdlib"]; base = "string_of_int" }
  | { path = ["Stdlib"]; base = "int_of_string" } -> { path = ["OCaml"; "Stdlib"]; base = "int_of_string" }
  (* Pair operations *)
  | { path = ["Stdlib"]; base = "fst" } -> { path = []; base = "fst" }
  | { path = ["Stdlib"]; base = "snd" } -> { path = []; base = "snd" }
  (* List operations *)
  | { path = ["Stdlib"]; base = "@" } -> { path = ["OCaml"; "Stdlib"]; base = "app" }
  (* Input/output *)
  (* Output functions on standard output *)
  | { path = ["Stdlib"]; base = "print_char" } -> { path = ["OCaml"; "Stdlib"]; base = "print_char" }
  | { path = ["Stdlib"]; base = "print_string" } -> { path = ["OCaml"; "Stdlib"]; base = "print_string" }
  | { path = ["Stdlib"]; base = "print_int" } -> { path = ["OCaml"; "Stdlib"]; base = "print_int" }
  | { path = ["Stdlib"]; base = "print_endline" } -> { path = ["OCaml"; "Stdlib"]; base = "print_endline" }
  | { path = ["Stdlib"]; base = "print_newline" } -> { path = ["OCaml"; "Stdlib"]; base = "print_newline" }
  (* Output functions on standard error *)
  | { path = ["Stdlib"]; base = "prerr_char" } -> { path = ["OCaml"; "Stdlib"]; base = "prerr_char" }
  | { path = ["Stdlib"]; base = "prerr_string" } -> { path = ["OCaml"; "Stdlib"]; base = "prerr_string" }
  | { path = ["Stdlib"]; base = "prerr_int" } -> { path = ["OCaml"; "Stdlib"]; base = "prerr_int" }
  | { path = ["Stdlib"]; base = "prerr_endline" } -> { path = ["OCaml"; "Stdlib"]; base = "prerr_endline" }
  | { path = ["Stdlib"]; base = "prerr_newline" } -> { path = ["OCaml"; "Stdlib"]; base = "prerr_newline" }
  (* Input functions on standard input *)
  | { path = ["Stdlib"]; base = "read_line" } -> { path = ["OCaml"; "Stdlib"]; base = "read_line" }
  | { path = ["Stdlib"]; base = "read_int" } -> { path = ["OCaml"; "Stdlib"]; base = "read_int" }
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Result type *)
  | { path = ["Stdlib"]; base = "result" } -> { path = []; base = "sum" }
  | { path = []; base = "Ok" } -> { path = []; base = "inl" }
  | { path = []; base = "Error" } -> { path = []; base = "inr" }
  (* Operations on format strings *)
  (* Program termination *)

  (* Bytes *)
  | { path = ["Stdlib"; "Bytes"]; base = "cat" } -> { path = ["String"]; base = "append" }
  | { path = ["Stdlib"; "Bytes"]; base = "concat" } -> { path = ["String"]; base = "concat" }
  | { path = ["Stdlib"; "Bytes"]; base = "length" } -> { path = ["String"]; base = "length" }
  | { path = ["Stdlib"; "Bytes"]; base = "sub" } -> { path = ["String"]; base = "sub" }

  (* List *)
  | { path = ["Stdlib"; "List"]; base = "exists" } -> { path = ["OCaml"; "List"]; base = "_exists" }
  | { path = ["Stdlib"; "List"]; base = "exists2" } -> { path = ["OCaml"; "List"]; base = "_exists2" }
  | { path = ["Stdlib"; "List"]; base = "map" } -> { path = ["List"]; base = "map" }
  | { path = ["Stdlib"; "List"]; base = "rev" } -> { path = ["List"]; base = "rev" }

  (* String *)
  | { path = ["Stdlib"; "String"]; base = "length" } -> { path = ["OCaml"; "String"]; base = "length" }

  | { path = path; base = base } -> { path = path; base = Name.convert base }

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path = path; base = base }

(** Import an OCaml [Longident.t]. *)
let of_long_ident (long_ident : Longident.t) : t =
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Longident.t with an empty list not expected."
  | x :: xs -> convert (of_name (List.rev xs) x)

(** Import an OCaml location. *)
let of_loc (loc : Longident.t loc) : t =
  of_long_ident loc.txt

(** Import an OCaml [Path.t]. *)
let of_path (path : Path.t) : t =
  let rec aux path : (Name.t list * Name.t) =
    match path with
    | Path.Pident x -> ([], Name.of_ident x)
    | Path.Pdot (path, s, _) ->
      let (path, base) = aux path in
      (base :: path, s)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  convert (of_name (List.rev path) base)

let of_path_and_name (path : Path.t) (name : Name.t) : t =
  let rec aux p : Name.t list * Name.t =
    match p with
    | Path.Pident x -> ([Name.of_ident x], name)
    | Path.Pdot (p, s, _) ->
      let (path, base) = aux p in
      (s :: path, base)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  convert (of_name (List.rev path) base)

let get_head_and_tail (path_name : t) : Name.t * t option =
  let { path; base } = path_name in
  match path with
  | [] -> (base, None)
  | head :: path -> (head, Some { path; base })

let add_prefix (prefix : Name.t) (path_name : t) : t =
  let { path; base } = path_name in
  { path = prefix :: path; base }

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))
