open SmartPrint
(** Local identifiers, used for variable names in patterns for example. *)

open Monad.Notations

(** Just a [string]. *)
type t = FunctionParameter | Make of string | Nameless

module Set = Set.Make (struct
  type nonrec t = t

  let compare = compare
end)

module Map = Map.Make (struct
  type nonrec t = t

  let compare = compare
end)

let equal (name1 : t) (name2 : t) : bool =
  match (name1, name2) with
  | FunctionParameter, FunctionParameter -> true
  | Make name1, Make name2 -> String.equal name1 name2
  | _ -> false

let escape_operator_character (c : char) : string =
  match c with
  | '=' -> "eq"
  | '<' -> "lt"
  | '>' -> "gt"
  | '@' -> "at"
  | '^' -> "caret"
  | '|' -> "pipe"
  | '&' -> "and"
  | '+' -> "plus"
  | '-' -> "minus"
  | '*' -> "star"
  | '/' -> "div"
  | '$' -> "dollar"
  | '%' -> "percent"
  | '?' -> "question"
  | '!' -> "exclamation"
  | '~' -> "tilde"
  | '.' -> "point"
  | ':' -> "colon"
  | _ -> String.make 1 c

let escape_operator (s : string) : string =
  let b = Buffer.create 0 in
  s |> String.iter (fun c -> Buffer.add_string b (escape_operator_character c));
  Buffer.contents b

let reserved_names : string list =
  [
    "at";
    "error";
    "exists";
    "exists2";
    "left";
    "mod";
    "pack";
    "return";
    "right";
    "Set";
    "Type";
    "Variable";
  ]

let native_type_constructors = [ "list"; "option" ]
let native_types = [ "int"; "string"; "bool"; "float"; "ascii"; "unit" ]

(** We only escape these names if they are used as values, as they may collide
    with the corresponding type names. *)
let value_names_to_escape : string list =
  [
    "bool";
    "bytes";
    "exn";
    "float";
    "int";
    "int32";
    "int64";
    "list";
    "nativeint";
    "option";
    "pair";
    "ref";
    "result";
    "string";
    "unit";
  ]

let escape_reserved_word (is_value : bool) (s : string) : string Monad.t =
  let* configuration = get_configuration in
  (* We always espace single letter values as they typically collide with type
     variables. *)
  let is_single_letter = String.length s = 1 && 'a' <= s.[0] && s.[0] <= 'z' in
  let is_value_to_escape =
    is_value
    && (is_single_letter
       || List.mem s value_names_to_escape
       || Configuration.is_value_to_escape configuration s)
  in
  if is_value_to_escape then return (s ^ "_value")
  else
    let is_reserved_name = List.mem s reserved_names in
    if is_reserved_name then return ("_" ^ s) else return s

let substitute_first_dollar (s : string) : string =
  if String.length s <> 0 && String.get s 0 = '$' then
    "__" ^ String.sub s 1 (String.length s - 1)
  else s

let convert (is_value : bool) (s : string) : string Monad.t =
  let s = substitute_first_dollar s in
  let s_escaped_operator = escape_operator s in
  if s_escaped_operator <> s then return ("op_" ^ s_escaped_operator)
  else escape_reserved_word is_value s

(** Lift a [string] to an identifier. *)
let of_string (is_value : bool) (s : string) : t Monad.t =
  convert is_value s >>= fun name -> return (Make name)

(** Lift a [string] to an identifier without doing conversion. *)
let of_string_raw (s : string) : t = Make s

(** Import an OCaml identifier. *)
let of_ident (is_value : bool) (i : Ident.t) : t Monad.t =
  of_string is_value (Ident.name i)

let of_optional_ident (is_value : bool) (i : Ident.t option) : t Monad.t =
  match i with None -> return Nameless | Some i -> of_ident is_value i

(** Import an OCaml identifier without doing conversion. *)
let of_ident_raw (i : Ident.t) : t = of_string_raw (Ident.name i)

let of_last_path (p : Path.t) : t = of_string_raw (Path.last p)

let of_strings (is_value : bool) (path : string list) : t Monad.t =
  of_string is_value (String.concat "_" path)

let to_string (name : t) : string =
  match name with
  | FunctionParameter -> "function_parameter"
  | Make name -> name
  | Nameless -> "_"

let prefix_by_single_quote (name : t) : t = Make ("'" ^ to_string name)
let prefix_by_t (name : t) : t = Make ("t_" ^ to_string name)
let prefix_by_with (name : t) : t = Make ("with_" ^ to_string name)
let suffix_by_include (name : t) : t = Make (to_string name ^ "_include")
let suffix_by_skeleton (name : t) : t = Make (to_string name ^ "_skeleton")
let arrow_tag = of_string_raw "arrow_tag"
let tuple_tag = of_string_raw "tuple_tag"
let constr_tag = of_string_raw "constr_tag"
let decode_vtag = of_string_raw "decode_vtag"

(** Pretty-print a name to Coq. *)
let to_coq (name : t) : SmartPrint.t = !^(to_string name)

let to_coq_list_or_empty (names : t list) (map : SmartPrint.t -> SmartPrint.t) :
    SmartPrint.t =
  match names with
  | [] -> empty
  | _ :: _ -> map (separate space (List.map to_coq names))

(** Not related to the name handling, but this is a good place to put it. *)
let string_of_optional_ident (ident : Ident.t option) : string =
  match ident with None -> "_" | Some ident -> Ident.name ident
