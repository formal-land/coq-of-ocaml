(** Local identifiers, used for variable names in patterns for example. *)
open SmartPrint

(** Just a [string]. *)
type t = Make of string

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

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
  s |> String.iter (fun c ->
    Buffer.add_string b (escape_operator_character c)
  );
  Buffer.contents b

let escape_reserved_word (is_value : bool) (s : string) : string =
  match s with
  | "bytes" -> if is_value then "__bytes_value" else s
  | "exists" -> "__exists"
  | "exists2" -> "__exists2"
  | "list" -> if is_value then "__list_value" else s
  | "mod" -> "__mod"
  | "option" -> if is_value then "__option_value" else s
  | "ref" -> if is_value then "__ref_value" else s
  | "return" -> "__return"
  | "string" -> if is_value then "__string_value" else s
  | "unit" -> if is_value then "__unit_value" else s
  | "Variable" -> "__Variable"
  | _ -> s

let convert (is_value : bool) (s : string) : string =
  let s_escaped_operator = escape_operator s in
  if s_escaped_operator <> s then
    "op_" ^ s_escaped_operator
  else
    escape_reserved_word is_value s

(** Lift a [string] to an identifier. *)
let of_string (is_value : bool) (s : string) : t =
  Make (convert is_value s)

(** Import an OCaml identifier. *)
let of_ident (is_value : bool) (i : Ident.t) : t =
  of_string is_value (Ident.name i)

let to_string (name : t) : string =
  let Make name = name in
  name

let prefix_by_single_quote (name : t) : t =
  let Make name = name in
  Make ("'" ^ name)

let suffix_by_gadt (name : t) : t =
  let Make name = name in
  Make (name ^ "_gadt")

let suffix_by_skeleton (name : t) : t =
  let Make name = name in
  Make (name ^ "_skeleton")

(** Pretty-print a name to Coq. *)
let to_coq (name : t) : SmartPrint.t =
  !^ (to_string name)
