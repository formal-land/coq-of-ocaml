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

let escape_reserved_word (s : string) : string =
  match s with
  | "exists" -> "__exists"
  | "return" -> "__return"
  | _ -> s

let convert (s : string) : string =
  let s_escaped_operator = escape_operator s in
  if s_escaped_operator <> s then
    "op_" ^ s_escaped_operator
  else
    escape_reserved_word s

(** Lift a [string] to an identifier. *)
let of_string (s : string) : t =
  Make (convert s)

(** Import an OCaml identifier. *)
let of_ident (i : Ident.t) : t =
  of_string (Ident.name i)

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
