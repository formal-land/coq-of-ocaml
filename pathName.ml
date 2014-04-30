(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open SmartPrint
open Yojson.Basic

type t = {
  path : Name.t list;
  base : Name.t }

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (x : t) : t =
  match x with
  | { path = ["Pervasives"]; base = "!" } -> { path = ["Pervasives"]; base = "!" }
  | { path = ["Pervasives"]; base = ":=" } -> { path = ["Pervasives"]; base = ":=" }
  (* The core library *)
  (* Built-in types *)
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
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

  (* Pervasives *)
  (* Exceptions *)
  | { path = ["Pervasives"]; base = "invalid_arg" } -> { path = ["OCaml"; "Pervasives"]; base = "invalid_arg" }
  | { path = ["Pervasives"]; base = "failwith" } -> { path = ["OCaml"; "Pervasives"]; base = "failwith" }
  | { path = []; base = "Exit" } | { path = ["Pervasives"]; base = "Exit" } ->
    { path = ["OCaml"; "Pervasives"]; base = "Exit" }
  (* Comparisons *)
  | { path = ["Pervasives"]; base = "=" } -> { path = []; base = "equiv_decb" }
  | { path = ["Pervasives"]; base = "<>" } -> { path = []; base = "nequiv_decb" }
  | { path = ["Pervasives"]; base = "<" } -> { path = ["OCaml"; "Pervasives"]; base = "lt" }
  | { path = ["Pervasives"]; base = ">" } -> { path = ["OCaml"; "Pervasives"]; base = "gt" }
  | { path = ["Pervasives"]; base = "<=" } -> { path = ["OCaml"; "Pervasives"]; base = "le" }
  | { path = ["Pervasives"]; base = ">=" } -> { path = ["OCaml"; "Pervasives"]; base = "ge" }
  | { path = ["Pervasives"]; base = "compare" } -> { path = ["OCaml"; "Pervasives"]; base = "compare" }
  | { path = ["Pervasives"]; base = "min" } -> { path = ["OCaml"; "Pervasives"]; base = "min" }
  | { path = ["Pervasives"]; base = "max" } -> { path = ["OCaml"; "Pervasives"]; base = "max" }
  (* Boolean operations *)
  | { path = ["Pervasives"]; base = "not" } -> { path = []; base = "negb" }
  | { path = ["Pervasives"]; base = "&&" } -> { path = []; base = "andb" }
  | { path = ["Pervasives"]; base = "&" } -> { path = []; base = "andb" }
  | { path = ["Pervasives"]; base = "||" } -> { path = []; base = "orb" }
  | { path = ["Pervasives"]; base = "or" } -> { path = []; base = "orb" }
  (* Composition operators *)
  | { path = ["Pervasives"]; base = "|>" } -> { path = ["OCaml"; "Pervasives"]; base = "reverse_apply" }
  | { path = ["Pervasives"]; base = "@@" } -> { path = []; base = "apply" }
  (* Integer arithmetic *)
  | { path = ["Pervasives"]; base = "~-" } -> { path = ["Z"]; base = "opp" }
  | { path = ["Pervasives"]; base = "~+" } -> { path = []; base = "" }
  | { path = ["Pervasives"]; base = "succ" } -> { path = ["Z"]; base = "succ" }
  | { path = ["Pervasives"]; base = "pred" } -> { path = ["Z"]; base = "pred" }
  | { path = ["Pervasives"]; base = "+" } -> { path = ["Z"]; base = "add" }
  | { path = ["Pervasives"]; base = "-" } -> { path = ["Z"]; base = "sub" }
  | { path = ["Pervasives"]; base = "*" } -> { path = ["Z"]; base = "mul" }
  | { path = ["Pervasives"]; base = "/" } -> { path = ["Z"]; base = "div" }
  | { path = ["Pervasives"]; base = "mod" } -> { path = ["Z"]; base = "modulo" }
  | { path = ["Pervasives"]; base = "abs" } -> { path = ["Z"]; base = "abs" }
  (* Bitwise operations *)
  | { path = ["Pervasives"]; base = "land" } -> { path = ["Z"]; base = "land" }
  | { path = ["Pervasives"]; base = "lor" } -> { path = ["Z"]; base = "lor" }
  | { path = ["Pervasives"]; base = "lxor" } -> { path = ["Z"]; base = "lxor" }
  | { path = ["Pervasives"]; base = "lsl" } -> { path = ["Z"]; base = "shiftl" }
  | { path = ["Pervasives"]; base = "lsr" } -> { path = ["Z"]; base = "shiftr" }
  (* Floating-point arithmetic *)
  (* String operations *)
  | { path = ["Pervasives"]; base = "^" } -> { path = ["String"]; base = "append" }
  (* Character operations *)
  | { path = ["Pervasives"]; base = "int_of_char" } -> { path = ["OCaml"; "Pervasives"]; base = "int_of_char" }
  | { path = ["Pervasives"]; base = "char_of_int" } -> { path = ["OCaml"; "Pervasives"]; base = "char_of_int" }
  (* Unit operations *)
  | { path = ["Pervasives"]; base = "ignore" } -> { path = ["OCaml"; "Pervasives"]; base = "ignore" }
  (* String conversion functions *)
  | { path = ["Pervasives"]; base = "string_of_bool" } -> { path = ["OCaml"; "Pervasives"]; base = "string_of_bool" }
  | { path = ["Pervasives"]; base = "bool_of_string" } -> { path = ["OCaml"; "Pervasives"]; base = "bool_of_string" }
  | { path = ["Pervasives"]; base = "string_of_int" } -> { path = ["OCaml"; "Pervasives"]; base = "string_of_int" }
  | { path = ["Pervasives"]; base = "int_of_string" } -> { path = ["OCaml"; "Pervasives"]; base = "int_of_string" }
  (* Pair operations *)
  | { path = ["Pervasives"]; base = "fst" } -> { path = []; base = "fst" }
  | { path = ["Pervasives"]; base = "snd" } -> { path = []; base = "snd" }
  (* List operations *)
  | { path = ["Pervasives"]; base = "@" } -> { path = ["OCaml"; "Pervasives"]; base = "app" }
  (* Input/output *)
  (* Output functions on standard output *)
  | { path = ["Pervasives"]; base = "print_char" } -> { path = ["OCaml"; "Pervasives"]; base = "print_char" }
  | { path = ["Pervasives"]; base = "print_string" } -> { path = ["OCaml"; "Pervasives"]; base = "print_string" }
  | { path = ["Pervasives"]; base = "print_int" } -> { path = ["OCaml"; "Pervasives"]; base = "print_int" }
  | { path = ["Pervasives"]; base = "print_endline" } -> { path = ["OCaml"; "Pervasives"]; base = "print_endline" }
  | { path = ["Pervasives"]; base = "print_newline" } -> { path = ["OCaml"; "Pervasives"]; base = "print_newline" }
  (* Output functions on standard error *)
  | { path = ["Pervasives"]; base = "prerr_char" } -> { path = ["OCaml"; "Pervasives"]; base = "prerr_char" }
  | { path = ["Pervasives"]; base = "prerr_string" } -> { path = ["OCaml"; "Pervasives"]; base = "prerr_string" }
  | { path = ["Pervasives"]; base = "prerr_int" } -> { path = ["OCaml"; "Pervasives"]; base = "prerr_int" }
  | { path = ["Pervasives"]; base = "prerr_endline" } -> { path = ["OCaml"; "Pervasives"]; base = "prerr_endline" }
  | { path = ["Pervasives"]; base = "prerr_newline" } -> { path = ["OCaml"; "Pervasives"]; base = "prerr_newline" }
  (* Input functions on standard input *)
  | { path = ["Pervasives"]; base = "read_line" } -> { path = ["OCaml"; "Pervasives"]; base = "read_line" }
  | { path = ["Pervasives"]; base = "read_int" } -> { path = ["OCaml"; "Pervasives"]; base = "read_int" }
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  | { path = ["List"]; base = "exists" } -> { path = ["OCaml"; "List"]; base = "_exists" }
  | { path = ["List"]; base = "exists2" } -> { path = ["OCaml"; "List"]; base = "_exists2" }

  | { path = path; base = base } -> { path = path; base = Name.convert base }

(** Pretty-print a global name. *)
let pp (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map (fun s -> !^ s) (x.path @ [x.base]))

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path = path; base = base }

(** Import an OCaml [Longident.t]. *)
let of_longident (longident : Longident.t) : t =
  match List.rev (Longident.flatten longident) with
  | [] ->
    failwith "TODO"; failwith "Longident.t with an empty list not expected."
  | x :: xs -> convert (of_name (List.rev xs) x)

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
    | Path.Papply _ -> failwith "TODO" in
  let (path, base) = aux p in
  convert (of_name (List.rev path) base)

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))

let to_json (x : t) : json =
  `String (String.concat "." (x.path @ [x.base]))

let of_json (json : json) : t =
  let rec split_at_last l =
    match l with
    | [] -> assert false
    | [x] -> ([], x)
    | x :: l ->
      let (path, base) = split_at_last l in
      (x :: path, base) in
  match json with
  | `String x ->
    let (path, base) = split_at_last @@ Str.split (Str.regexp_string ".") x in
    of_name path base
  | _ -> failwith "List expected."