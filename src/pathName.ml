(** Global identifiers with a module path, used to reference a definition for example. *)
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

(* Convert an identifier from OCaml to its Coq's equivalent, or [None] if no
   conversion is needed. We consider all the paths in the standard library
   to be converted, as conversion also means keeping the name as it (without
   taking into accounts that the stdlib was open). *)
let try_convert (path_name : t) : t option =
  let { path; base } = path_name in
  match path with
  (* The core library *)
  | [] ->
    begin match base with
    (* Built-in types *)
    | "int" -> Some { path = []; base = "Z" }
    | "float" -> Some { path = []; base = "Z" }
    | "char" -> Some { path = []; base = "ascii" }
    | "bytes" -> Some { path = []; base = "string" }
    | "string" -> Some { path = []; base = "string" }
    | "bool" -> Some { path = []; base = "bool" }
    | "false" -> Some { path = []; base = "false" }
    | "true" -> Some { path = []; base = "true" }
    | "unit" -> Some { path = []; base = "unit" }
    | "()" -> Some { path = []; base = "tt" }
    | "list" -> Some { path = []; base = "list" }
    | "[]" -> Some { path = []; base = "[]" }
    | "::" -> Some { path = []; base = "cons" }
    | "option" -> Some { path = []; base = "option" }
    | "None" -> Some { path = []; base = "None" }
    | "Some" -> Some { path = []; base = "Some" }
    | "Ok" -> Some { path = []; base = "inl" }
    | "Error" -> Some { path = []; base = "inr" }

    (* Predefined exceptions *)
    | "Match_failure" -> Some { path = ["OCaml"]; base = "Match_failure" }
    | "Assert_failure" -> Some { path = ["OCaml"]; base = "Assert_failure" }
    | "Invalid_argument" -> Some { path = ["OCaml"]; base = "Invalid_argument" }
    | "Failure" -> Some { path = ["OCaml"]; base = "Failure" }
    | "Not_found" -> Some { path = ["OCaml"]; base = "Not_found" }
    | "Out_of_memory" -> Some { path = ["OCaml"]; base = "Out_of_memory" }
    | "Stack_overflow" -> Some { path = ["OCaml"]; base = "Stack_overflow" }
    | "Sys_error" -> Some { path = ["OCaml"]; base = "Sys_error" }
    | "End_of_file" -> Some { path = ["OCaml"]; base = "End_of_file" }
    | "Division_by_zero" -> Some { path = ["OCaml"]; base = "Division_by_zero" }
    | "Sys_blocked_io" -> Some { path = ["OCaml"]; base = "Sys_blocked_io" }
    | "Undefined_recursive_module" -> Some { path = ["OCaml"]; base = "Undefined_recursive_module" }
    | _ -> None
    end

  (* Optional parameters *)
  | ["*predef*"] ->
    begin match base with
    | "None" -> Some { path = []; base = "None" }
    | "Some" -> Some { path = []; base = "Some" }
    | _ -> None
    end

  (* Stdlib *)
  | [lib_name] when lib_name = stdlib_name ->
    begin match base with
    (* Exceptions *)
    | "invalid_arg" -> Some { path = ["OCaml"; "Stdlib"]; base = "invalid_arg" }
    | "failwith" -> Some { path = ["OCaml"; "Stdlib"]; base = "failwith" }
    | "Exit" -> Some { path = ["OCaml"; "Stdlib"]; base = "Exit" }
    (* Comparisons *)
    | "=" -> Some { path = []; base = "equiv_decb" }
    | "<>" -> Some { path = []; base = "nequiv_decb" }
    | "<" -> Some { path = ["OCaml"; "Stdlib"]; base = "lt" }
    | ">" -> Some { path = ["OCaml"; "Stdlib"]; base = "gt" }
    | "<=" -> Some { path = ["OCaml"; "Stdlib"]; base = "le" }
    | ">=" -> Some { path = ["OCaml"; "Stdlib"]; base = "ge" }
    | "compare" -> Some { path = ["OCaml"; "Stdlib"]; base = "compare" }
    | "min" -> Some { path = ["OCaml"; "Stdlib"]; base = "min" }
    | "max" -> Some { path = ["OCaml"; "Stdlib"]; base = "max" }
    (* Boolean operations *)
    | "not" -> Some { path = []; base = "negb" }
    | "&&" -> Some { path = []; base = "andb" }
    | "&" -> Some { path = []; base = "andb" }
    | "||" -> Some { path = []; base = "orb" }
    | "or" -> Some { path = []; base = "orb" }
    (* Composition operators *)
    | "|>" -> Some { path = ["OCaml"; "Stdlib"]; base = "reverse_apply" }
    | "@@" -> Some { path = []; base = "apply" }
    (* Integer arithmetic *)
    | "~-" -> Some { path = ["Z"]; base = "opp" }
    | "~+" -> Some { path = []; base = "" }
    | "succ" -> Some { path = ["Z"]; base = "succ" }
    | "pred" -> Some { path = ["Z"]; base = "pred" }
    | "+" -> Some { path = ["Z"]; base = "add" }
    | "-" -> Some { path = ["Z"]; base = "sub" }
    | "*" -> Some { path = ["Z"]; base = "mul" }
    | "/" -> Some { path = ["Z"]; base = "div" }
    | "mod" -> Some { path = ["Z"]; base = "modulo" }
    | "abs" -> Some { path = ["Z"]; base = "abs" }
    (* Bitwise operations *)
    | "land" -> Some { path = ["Z"]; base = "land" }
    | "lor" -> Some { path = ["Z"]; base = "lor" }
    | "lxor" -> Some { path = ["Z"]; base = "lxor" }
    | "lsl" -> Some { path = ["Z"]; base = "shiftl" }
    | "lsr" -> Some { path = ["Z"]; base = "shiftr" }
    (* Floating-point arithmetic *)
    (* String operations *)
    | "^" -> Some { path = ["String"]; base = "append" }
    (* Character operations *)
    | "int_of_char" -> Some { path = ["OCaml"; "Stdlib"]; base = "int_of_char" }
    | "char_of_int" -> Some { path = ["OCaml"; "Stdlib"]; base = "char_of_int" }
    (* Unit operations *)
    | "ignore" -> Some { path = ["OCaml"; "Stdlib"]; base = "ignore" }
    (* String conversion functions *)
    | "string_of_bool" -> Some { path = ["OCaml"; "Stdlib"]; base = "string_of_bool" }
    | "bool_of_string" -> Some { path = ["OCaml"; "Stdlib"]; base = "bool_of_string" }
    | "string_of_int" -> Some { path = ["OCaml"; "Stdlib"]; base = "string_of_int" }
    | "int_of_string" -> Some { path = ["OCaml"; "Stdlib"]; base = "int_of_string" }
    (* Pair operations *)
    | "fst" -> Some { path = []; base = "fst" }
    | "snd" -> Some { path = []; base = "snd" }
    (* List operations *)
    | "@" -> Some { path = ["OCaml"; "Stdlib"]; base = "app" }
    (* Input/output *)
    (* Output functions on standard output *)
    | "print_char" -> Some { path = ["OCaml"; "Stdlib"]; base = "print_char" }
    | "print_string" -> Some { path = ["OCaml"; "Stdlib"]; base = "print_string" }
    | "print_int" -> Some { path = ["OCaml"; "Stdlib"]; base = "print_int" }
    | "print_endline" -> Some { path = ["OCaml"; "Stdlib"]; base = "print_endline" }
    | "print_newline" -> Some { path = ["OCaml"; "Stdlib"]; base = "print_newline" }
    (* Output functions on standard error *)
    | "prerr_char" -> Some { path = ["OCaml"; "Stdlib"]; base = "prerr_char" }
    | "prerr_string" -> Some { path = ["OCaml"; "Stdlib"]; base = "prerr_string" }
    | "prerr_int" -> Some { path = ["OCaml"; "Stdlib"]; base = "prerr_int" }
    | "prerr_endline" -> Some { path = ["OCaml"; "Stdlib"]; base = "prerr_endline" }
    | "prerr_newline" -> Some { path = ["OCaml"; "Stdlib"]; base = "prerr_newline" }
    (* Input functions on standard input *)
    | "read_line" -> Some { path = ["OCaml"; "Stdlib"]; base = "read_line" }
    | "read_int" -> Some { path = ["OCaml"; "Stdlib"]; base = "read_int" }
    (* General output functions *)
    (* General input functions *)
    (* Operations on large files *)
    (* References *)
    (* Result type *)
    | "result" -> Some { path = []; base = "sum" }
    (* Operations on format strings *)
    (* Program termination *)
    | _ -> Some path_name
    end

  (* Bytes *)
  | [lib_name; "Bytes"] when lib_name = stdlib_name ->
    begin match base with
    | "cat" -> Some { path = ["String"]; base = "append" }
    | "concat" -> Some { path = ["String"]; base = "concat" }
    | "length" -> Some { path = ["String"]; base = "length" }
    | "sub" -> Some { path = ["String"]; base = "sub" }
    | _ -> Some path_name
    end

  (* List *)
  | [lib_name; "List"] when lib_name = stdlib_name ->
    begin match base with
    | "exists" -> Some { path = ["OCaml"; "List"]; base = "_exists" }
    | "exists2" -> Some { path = ["OCaml"; "List"]; base = "_exists2" }
    | "length" -> Some { path = ["OCaml"; "List"]; base = "length" }
    | "map" -> Some { path = ["List"]; base = "map" }
    | "rev" -> Some { path = ["List"]; base = "rev" }
    | _ -> Some path_name
    end

  (* String *)
  | [lib_name; "String"] when lib_name = stdlib_name ->
    begin match base with
    | "length" -> Some { path = ["OCaml"; "String"]; base = "length" }
    | _ -> Some path_name
    end

  | _ -> None

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

(** Import an OCaml [Longident.t]. *)
let of_long_ident (long_ident : Longident.t) : t =
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Unexpected Longident.t with an empty list"
  | x :: xs -> of_name (xs |> List.rev |> List.map Name.convert) (Name.convert x)

(** Import an OCaml [Path.t]. *)
let of_path_without_convert (path : Path.t) : t =
  let rec aux path : (Name.t list * Name.t) =
    match path with
    | Path.Pident x -> ([], Name.of_ident x)
    | Path.Pdot (path, s, _) ->
      let (path, base) = aux path in
      (base :: path, s)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  of_name (List.rev path) base

let of_path_with_convert (path : Path.t) : t =
  let path_name = of_path_without_convert path in
  match try_convert path_name with
  | None -> path_name
  | Some path_name -> path_name

let of_path_and_name_without_convert (path : Path.t) (name : Name.t) : t =
  let rec aux p : Name.t list * Name.t =
    match p with
    | Path.Pident x -> ([Name.of_ident x], name)
    | Path.Pdot (p, s, _) ->
      let (path, base) = aux p in
      (s :: path, base)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  of_name (List.rev path) base

let of_constructor_description (constructor_description : Types.constructor_description) : t =
  match constructor_description with
  | { cstr_name; cstr_res = { desc = Tconstr (path, _, _); _ } ; _ } ->
    let { path; _ } = of_path_without_convert path in
    let path_name = { path; base = cstr_name } in
    begin match try_convert path_name with
    | None -> path_name
    | Some path_name -> path_name
    end
  | _ -> failwith "Unexpected constructor description without a constructor type"

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
