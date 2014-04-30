(** Local identifiers, used for variable names in patterns for example. *)
open Typedtree
open SmartPrint
open Yojson.Basic

(** Just a [string] (no freshness counter for now). *)
type t = string

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

let pp (x : t) : SmartPrint.t =
  !^ x

let is_operator (s : string) : bool =
  if s = "" then
    failwith "Unexpected empty argument."
  else
    let c = Char.code s.[0] in
    not (c = Char.code '_' ||
      (Char.code 'a' <= c && c <= Char.code 'z') ||
      (Char.code 'A' <= c && c <= Char.code 'Z') ||
      (Char.code '0' <= c && c <= Char.code '9'))

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
  | _ -> failwith "Unexpected character for an operator."

let escape_operator (s : string) : string =
  let b = Buffer.create 0 in
  s |> String.iter (fun c ->
    Buffer.add_char b '_';
    Buffer.add_string b (escape_operator_character c));
  Buffer.contents b

let convert (x : t) : t =
  if is_operator x then
    "op" ^ escape_operator x
  else
    x

(** Import an OCaml identifier. *)
let of_ident (i : Ident.t) : t =
  convert i.Ident.name

(** Lift a [string] to an identifier. *)
let of_string (s : string) : t =
  s

(** Generate a fresh name from a given [prefix] using an internal counter. *)
let unsafe_fresh : string -> t =
  let counters : int Map.t ref = ref Map.empty in
  fun prefix ->
    if not (Map.mem prefix !counters) then
      counters := Map.add prefix 0 !counters;
    let n = Map.find prefix !counters in
    counters := Map.add prefix (n + 1) !counters;
    Printf.sprintf "%s_%d" prefix n

(** Pretty-print a name to Coq. *)
let to_coq (x : t) : SmartPrint.t =
  !^ x

let to_json (x : t) : json =
  `String x

let of_json (json : json) : t =
  match json with
  | `String x -> x
  | _ -> failwith "TODO"(*raise (Error.Json "String expected.")*)