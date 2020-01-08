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
  let make (path : string list) (base : string) : t option =
    Some { path = path |> List.map (fun name -> Name.Make name); base = Name.Make base } in
  let { path; base } = path_name in
  match path |> List.map Name.to_string with
  (* The core library *)
  | [] ->
    begin match Name.to_string base with
    (* Built-in types *)
    | "int" -> make [] "Z"
    | "float" -> make [] "Z"
    | "char" -> make [] "ascii"
    | "bytes" -> make [] "string"
    | "string" -> make [] "string"
    | "bool" -> make [] "bool"
    | "false" -> make [] "false"
    | "true" -> make [] "true"
    | "unit" -> make [] "unit"
    | "()" -> make [] "tt"
    | "list" -> make [] "list"
    | "[]" -> make [] "[]"
    | "op_coloncolon" -> make [] "cons"
    | "option" -> make [] "option"
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | "Ok" -> make [] "inl"
    | "Error" -> make [] "inr"

    (* Predefined exceptions *)
    | "Match_failure" -> make ["OCaml"] "Match_failure"
    | "Assert_failure" -> make ["OCaml"] "Assert_failure"
    | "Invalid_argument" -> make ["OCaml"] "Invalid_argument"
    | "Failure" -> make ["OCaml"] "Failure"
    | "Not_found" -> make ["OCaml"] "Not_found"
    | "Out_of_memory" -> make ["OCaml"] "Out_of_memory"
    | "Stack_overflow" -> make ["OCaml"] "Stack_overflow"
    | "Sys_error" -> make ["OCaml"] "Sys_error"
    | "End_of_file" -> make ["OCaml"] "End_of_file"
    | "Division_by_zero" -> make ["OCaml"] "Division_by_zero"
    | "Sys_blocked_io" -> make ["OCaml"] "Sys_blocked_io"
    | "Undefined_recursive_module" -> make ["OCaml"] "Undefined_recursive_module"
    | _ -> None
    end

  (* Optional parameters *)
  | ["*predef*"] ->
    begin match Name.to_string base with
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | _ -> None
    end

  (* Stdlib *)
  | [lib_name] when lib_name = stdlib_name ->
    begin match Name.to_string base with
    (* Exceptions *)
    | "invalid_arg" -> make ["OCaml"; "Stdlib"] "invalid_arg"
    | "failwith" -> make ["OCaml"; "Stdlib"] "failwith"
    | "Exit" -> make ["OCaml"; "Stdlib"] "Exit"
    (* Comparisons *)
    | "op_eq" -> make [] "equiv_decb"
    | "op_ltgt" -> make [] "nequiv_decb"
    | "op_lt" -> make ["OCaml"; "Stdlib"] "lt"
    | "op_gt" -> make ["OCaml"; "Stdlib"] "gt"
    | "op_lteq" -> make ["OCaml"; "Stdlib"] "le"
    | "op_gteq" -> make ["OCaml"; "Stdlib"] "ge"
    | "compare" -> make ["OCaml"; "Stdlib"] "compare"
    | "min" -> make ["OCaml"; "Stdlib"] "min"
    | "max" -> make ["OCaml"; "Stdlib"] "max"
    (* Boolean operations *)
    | "not" -> make [] "negb"
    | "op_andand" -> make [] "andb"
    | "op_and" -> make [] "andb"
    | "op_pipepipe" -> make [] "orb"
    | "or" -> make [] "orb"
    (* Composition operators *)
    | "op_pipegt" -> make ["OCaml"; "Stdlib"] "reverse_apply"
    | "op_atat" -> make [] "apply"
    (* Integer arithmetic *)
    | "op_tildeminus" -> make ["Z"] "opp"
    | "op_tildeplus" -> make []  ""
    | "succ" -> make ["Z"] "succ"
    | "pred" -> make ["Z"] "pred"
    | "op_plus" -> make ["Z"] "add"
    | "op_minus" -> make ["Z"] "sub"
    | "op_star" -> make ["Z"] "mul"
    | "op_div" -> make ["Z"] "div"
    | "__mod" -> make ["Z"] "modulo"
    | "abs" -> make ["Z"] "abs"
    (* Bitwise operations *)
    | "land" -> make ["Z"] "land"
    | "lor" -> make ["Z"] "lor"
    | "lxor" -> make ["Z"] "lxor"
    | "lsl" -> make ["Z"] "shiftl"
    | "lsr" -> make ["Z"] "shiftr"
    (* Floating-point arithmetic *)
    (* String operations *)
    | "op_caret" -> make ["String"] "append"
    (* Character operations *)
    | "int_of_char" -> make ["OCaml"; "Stdlib"] "int_of_char"
    | "char_of_int" -> make ["OCaml"; "Stdlib"] "char_of_int"
    (* Unit operations *)
    | "ignore" -> make ["OCaml"; "Stdlib"] "ignore"
    (* String conversion functions *)
    | "string_of_bool" -> make ["OCaml"; "Stdlib"] "string_of_bool"
    | "bool_of_string" -> make ["OCaml"; "Stdlib"] "bool_of_string"
    | "string_of_int" -> make ["OCaml"; "Stdlib"] "string_of_int"
    | "int_of_string" -> make ["OCaml"; "Stdlib"] "int_of_string"
    (* Pair operations *)
    | "fst" -> make [] "fst"
    | "snd" -> make [] "snd"
    (* List operations *)
    | "op_at" -> make ["OCaml"; "Stdlib"] "app"
    (* Input/output *)
    (* Output functions on standard output *)
    | "print_char" -> make ["OCaml"; "Stdlib"] "print_char"
    | "print_string" -> make ["OCaml"; "Stdlib"] "print_string"
    | "print_int" -> make ["OCaml"; "Stdlib"] "print_int"
    | "print_endline" -> make ["OCaml"; "Stdlib"] "print_endline"
    | "print_newline" -> make ["OCaml"; "Stdlib"] "print_newline"
    (* Output functions on standard error *)
    | "prerr_char" -> make ["OCaml"; "Stdlib"] "prerr_char"
    | "prerr_string" -> make ["OCaml"; "Stdlib"] "prerr_string"
    | "prerr_int" -> make ["OCaml"; "Stdlib"] "prerr_int"
    | "prerr_endline" -> make ["OCaml"; "Stdlib"] "prerr_endline"
    | "prerr_newline" -> make ["OCaml"; "Stdlib"] "prerr_newline"
    (* Input functions on standard input *)
    | "read_line" -> make ["OCaml"; "Stdlib"] "read_line"
    | "read_int" -> make ["OCaml"; "Stdlib"] "read_int"
    (* General output functions *)
    (* General input functions *)
    (* Operations on large files *)
    (* References *)
    (* Result type *)
    | "result" -> make [] "sum"
    (* Operations on format strings *)
    (* Program termination *)
    | _ -> Some path_name
    end

  (* Bytes *)
  | [lib_name; "Bytes"] when lib_name = stdlib_name ->
    begin match Name.to_string base with
    | "cat" -> make ["String"] "append"
    | "concat" -> make ["String"] "concat"
    | "length" -> make ["String"] "length"
    | "sub" -> make ["String"] "sub"
    | _ -> Some path_name
    end

  (* List *)
  | [lib_name; "List"] when lib_name = stdlib_name ->
    begin match Name.to_string base with
    | "exists" -> make ["OCaml"; "List"] "_exists"
    | "exists2" -> make ["OCaml"; "List"] "_exists2"
    | "length" -> make ["OCaml"; "List"] "length"
    | "map" -> make ["List"] "map"
    | "rev" -> make ["List"] "rev"
    | _ -> Some path_name
    end

  (* String *)
  | [lib_name; "String"] when lib_name = stdlib_name ->
    begin match Name.to_string base with
    | "length" -> make ["OCaml"; "String"] "length"
    | _ -> Some path_name
    end

  | _ -> None

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

(** Import an OCaml [Longident.t]. *)
let of_long_ident (is_value : bool) (long_ident : Longident.t) : t =
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Unexpected Longident.t with an empty list"
  | x :: xs ->
    of_name
      (xs |> List.rev |> List.map (Name.of_string is_value))
      (Name.of_string is_value x)

(** Import an OCaml [Path.t]. *)
let of_path_without_convert (is_value : bool) (path : Path.t) : t =
  let rec aux path : (Name.t list * Name.t) =
    match path with
    | Path.Pident x -> ([], Name.of_ident is_value x)
    | Path.Pdot (path, s, _) ->
      let (path, base) = aux path in
      (base :: path, Name.of_string is_value s)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  of_name (List.rev path) base

let of_path_with_convert (is_value : bool) (path : Path.t) : t =
  let path_name = of_path_without_convert is_value path in
  match try_convert path_name with
  | None -> path_name
  | Some path_name -> path_name

let of_path_and_name_without_convert (path : Path.t) (name : Name.t) : t =
  let rec aux p : Name.t list * Name.t =
    match p with
    | Path.Pident x -> ([Name.of_ident false x], name)
    | Path.Pdot (p, s, _) ->
      let (path, base) = aux p in
      (Name.of_string false s :: path, base)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  of_name (List.rev path) base

let of_constructor_description
  (constructor_description : Types.constructor_description)
  : t =
  match constructor_description with
  | { cstr_name; cstr_res = { desc = Tconstr (path, _, _); _ } ; _ } ->
    let { path; _ } = of_path_without_convert false path in
    let path_name = { path; base = Name.of_string false cstr_name } in
    begin match try_convert path_name with
    | None -> path_name
    | Some path_name -> path_name
    end
  | _ -> failwith "Unexpected constructor description without a type constructor"

let of_label_description (label_description : Types.label_description) : t =
  match label_description with
  | { lbl_name; lbl_res = { desc = Tconstr (path, _, _); _ } ; _ } ->
    let { path; base } = of_path_without_convert false path in
    let path_name = {
      path = path @ [base];
      base = Name.of_string false lbl_name } in
    begin match try_convert path_name with
    | None -> path_name
    | Some path_name -> path_name
    end
  | _ -> failwith "Unexpected label description without a type constructor"

let get_head_and_tail (path_name : t) : Name.t * t option =
  let { path; base } = path_name in
  match path with
  | [] -> (base, None)
  | head :: path -> (head, Some { path; base })

let add_prefix (prefix : Name.t) (path_name : t) : t =
  let { path; base } = path_name in
  { path = prefix :: path; base }

let is_unit (path_name : t) : bool =
  match (path_name.path, Name.to_string path_name.base) with
  | ([], "unit") -> true
  | _ -> false

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))
