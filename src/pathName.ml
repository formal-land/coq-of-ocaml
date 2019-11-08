(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open SmartPrint

type t = {
  path : Name.t list;
  base : Name.t }

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

let stdlib_name =
  if Sys.ocaml_version >= "4.07" then
    "Stdlib"
  else
    "Pervasives"

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert ({ path; base } : t) : t =
  let default = { path; base = Name.convert base } in
  match path with
  (* The core library *)
  | [] ->
    begin match base with
    (* Built-in types *)
    | "int" -> { path = []; base = "Z" }
    | "float" -> { path = []; base = "Z" }
    | "char" -> { path = []; base = "ascii" }
    | "bytes" -> { path = []; base = "string" }
    | "string" -> { path = []; base = "string" }
    | "bool" -> { path = []; base = "bool" }
    | "false" -> { path = []; base = "false" }
    | "true" -> { path = []; base = "true" }
    | "unit" -> { path = []; base = "unit" }
    | "()" -> { path = []; base = "tt" }
    | "list" -> { path = []; base = "list" }
    | "[]" -> { path = []; base = "[]" }
    | "::" -> { path = []; base = "cons" }
    | "option" -> { path = []; base = "option" }
    | "None" -> { path = []; base = "None" }
    | "Some" -> { path = []; base = "Some" }
    | "Ok" -> { path = []; base = "inl" }
    | "Error" -> { path = []; base = "inr" }

    (* Predefined exceptions *)
    | "Match_failure" -> { path = ["OCaml"]; base = "Match_failure" }
    | "Assert_failure" -> { path = ["OCaml"]; base = "Assert_failure" }
    | "Invalid_argument" -> { path = ["OCaml"]; base = "Invalid_argument" }
    | "Failure" -> { path = ["OCaml"]; base = "Failure" }
    | "Not_found" -> { path = ["OCaml"]; base = "Not_found" }
    | "Out_of_memory" -> { path = ["OCaml"]; base = "Out_of_memory" }
    | "Stack_overflow" -> { path = ["OCaml"]; base = "Stack_overflow" }
    | "Sys_error" -> { path = ["OCaml"]; base = "Sys_error" }
    | "End_of_file" -> { path = ["OCaml"]; base = "End_of_file" }
    | "Division_by_zero" -> { path = ["OCaml"]; base = "Division_by_zero" }
    | "Sys_blocked_io" -> { path = ["OCaml"]; base = "Sys_blocked_io" }
    | "Undefined_recursive_module" -> { path = ["OCaml"]; base = "Undefined_recursive_module" }
    | _ -> default
    end

  (* Optional parameters *)
  | ["*predef*"] ->
    begin match base with
    | "None" -> { path = []; base = "None" }
    | "Some" -> { path = []; base = "Some" }
    | _ -> default
    end

  (* Stdlib *)
  | [lib_name] when lib_name = stdlib_name ->
    begin match base with
    (* Exceptions *)
    | "invalid_arg" -> { path = ["OCaml"; "Stdlib"]; base = "invalid_arg" }
    | "failwith" -> { path = ["OCaml"; "Stdlib"]; base = "failwith" }
    | "Exit" ->
      { path = ["OCaml"; "Stdlib"]; base = "Exit" }
    (* Comparisons *)
    | "=" -> { path = []; base = "equiv_decb" }
    | "<>" -> { path = []; base = "nequiv_decb" }
    | "<" -> { path = ["OCaml"; "Stdlib"]; base = "lt" }
    | ">" -> { path = ["OCaml"; "Stdlib"]; base = "gt" }
    | "<=" -> { path = ["OCaml"; "Stdlib"]; base = "le" }
    | ">=" -> { path = ["OCaml"; "Stdlib"]; base = "ge" }
    | "compare" -> { path = ["OCaml"; "Stdlib"]; base = "compare" }
    | "min" -> { path = ["OCaml"; "Stdlib"]; base = "min" }
    | "max" -> { path = ["OCaml"; "Stdlib"]; base = "max" }
    (* Boolean operations *)
    | "not" -> { path = []; base = "negb" }
    | "&&" -> { path = []; base = "andb" }
    | "&" -> { path = []; base = "andb" }
    | "||" -> { path = []; base = "orb" }
    | "or" -> { path = []; base = "orb" }
    (* Composition operators *)
    | "|>" -> { path = ["OCaml"; "Stdlib"]; base = "reverse_apply" }
    | "@@" -> { path = []; base = "apply" }
    (* Integer arithmetic *)
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
    (* Bitwise operations *)
    | "land" -> { path = ["Z"]; base = "land" }
    | "lor" -> { path = ["Z"]; base = "lor" }
    | "lxor" -> { path = ["Z"]; base = "lxor" }
    | "lsl" -> { path = ["Z"]; base = "shiftl" }
    | "lsr" -> { path = ["Z"]; base = "shiftr" }
    (* Floating-point arithmetic *)
    (* String operations *)
    | "^" -> { path = ["String"]; base = "append" }
    (* Character operations *)
    | "int_of_char" -> { path = ["OCaml"; "Stdlib"]; base = "int_of_char" }
    | "char_of_int" -> { path = ["OCaml"; "Stdlib"]; base = "char_of_int" }
    (* Unit operations *)
    | "ignore" -> { path = ["OCaml"; "Stdlib"]; base = "ignore" }
    (* String conversion functions *)
    | "string_of_bool" -> { path = ["OCaml"; "Stdlib"]; base = "string_of_bool" }
    | "bool_of_string" -> { path = ["OCaml"; "Stdlib"]; base = "bool_of_string" }
    | "string_of_int" -> { path = ["OCaml"; "Stdlib"]; base = "string_of_int" }
    | "int_of_string" -> { path = ["OCaml"; "Stdlib"]; base = "int_of_string" }
    (* Pair operations *)
    | "fst" -> { path = []; base = "fst" }
    | "snd" -> { path = []; base = "snd" }
    (* List operations *)
    | "@" -> { path = ["OCaml"; "Stdlib"]; base = "app" }
    (* Input/output *)
    (* Output functions on standard output *)
    | "print_char" -> { path = ["OCaml"; "Stdlib"]; base = "print_char" }
    | "print_string" -> { path = ["OCaml"; "Stdlib"]; base = "print_string" }
    | "print_int" -> { path = ["OCaml"; "Stdlib"]; base = "print_int" }
    | "print_endline" -> { path = ["OCaml"; "Stdlib"]; base = "print_endline" }
    | "print_newline" -> { path = ["OCaml"; "Stdlib"]; base = "print_newline" }
    (* Output functions on standard error *)
    | "prerr_char" -> { path = ["OCaml"; "Stdlib"]; base = "prerr_char" }
    | "prerr_string" -> { path = ["OCaml"; "Stdlib"]; base = "prerr_string" }
    | "prerr_int" -> { path = ["OCaml"; "Stdlib"]; base = "prerr_int" }
    | "prerr_endline" -> { path = ["OCaml"; "Stdlib"]; base = "prerr_endline" }
    | "prerr_newline" -> { path = ["OCaml"; "Stdlib"]; base = "prerr_newline" }
    (* Input functions on standard input *)
    | "read_line" -> { path = ["OCaml"; "Stdlib"]; base = "read_line" }
    | "read_int" -> { path = ["OCaml"; "Stdlib"]; base = "read_int" }
    (* General output functions *)
    (* General input functions *)
    (* Operations on large files *)
    (* References *)
    (* Result type *)
    | "result" -> { path = []; base = "sum" }
    (* Operations on format strings *)
    (* Program termination *)
    | _ -> default
    end

  (* Bytes *)
  | [lib_name; "Bytes"] when lib_name = stdlib_name ->
    begin match base with
    | "cat" -> { path = ["String"]; base = "append" }
    | "concat" -> { path = ["String"]; base = "concat" }
    | "length" -> { path = ["String"]; base = "length" }
    | "sub" -> { path = ["String"]; base = "sub" }
    | _ -> default
    end

  (* List *)
  | [lib_name; "List"] when lib_name = stdlib_name ->
    begin match base with
    | "exists" -> { path = ["OCaml"; "List"]; base = "_exists" }
    | "exists2" -> { path = ["OCaml"; "List"]; base = "_exists2" }
    | "length" -> { path = ["OCaml"; "List"]; base = "length" }
    | "map" -> { path = ["List"]; base = "map" }
    | "rev" -> { path = ["List"]; base = "rev" }
    | _ -> default
    end

  (* String *)
  | [lib_name; "String"] when lib_name = stdlib_name ->
    begin match base with
    | "length" -> { path = ["OCaml"; "String"]; base = "length" }
    | _ -> default
    end

  | _ -> default

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

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
