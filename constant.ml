(** Constants. *)
open Asttypes
open SmartPrint

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
let pp (c : t) : SmartPrint.t =
  match c with
  | Int n ->
    if n >= 0 then
      OCaml.int n
    else
      parens @@ OCaml.int n
  | Char c -> nest (double_quotes (!^ (Char.escaped c)) ^^ !^ "%" ^^ !^ "char")
  | String s -> nest (OCaml.string s ^^ !^ "%" ^^ !^ "string")
