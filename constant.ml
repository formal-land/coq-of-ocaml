(** Constants. *)
open Asttypes
open PPrint

type t =
  | Int of int
  | Char of char
  | String of string

(** Import an OCaml constant. *)
let of_constant (c : constant) : t =
  match c with
  | Const_int n -> Int n
  | Const_char c -> Char c
  | Const_string (s, _) -> String s
  | _ -> failwith "Constant not handled."

(** Pretty-print a constant. *)
let pp (c : t) : document =
  match c with
  | Int n ->
    if n >= 0 then
      OCaml.int n
    else
      lparen ^^ OCaml.int n ^^ rparen
  | Char c -> group (flow (break 1) [!^ "\"" ^^ !^ (Char.escaped c) ^^ !^ "\""; !^ "%"; !^ "char"])
  | String s -> group (flow (break 1) [OCaml.string s; !^ "%"; !^ "string"])
