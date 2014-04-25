(** Constants. *)
open Asttypes
open SmartPrint

type t =
  | Int of int
  | Nat of int
  | Char of char
  | String of string

let pp (c : t) : SmartPrint.t =
  match c with
  | Int n -> !^ "Int" ^-^ parens (OCaml.int n)
  | Nat n -> !^ "Nat" ^-^ parens (OCaml.int n)
  | Char c -> !^ "Char" ^-^ parens (OCaml.string (Char.escaped c))
  | String s -> !^ "String" ^-^ parens (OCaml.string s)

(** Import an OCaml constant. *)
let of_constant (loc : Loc.t) (c : constant) : t =
  match c with
  | Const_int n -> Int n
  | Const_char c -> Char c
  | Const_string (s, _) -> String s
  | Const_float s ->
    let n = int_of_float (float_of_string s) in
    Error.warn loc (Printf.sprintf "Float constant %s is approximated by the integer %d." s n);
    Int n
  | Const_int32 n ->
    Error.warn loc "Constant of type int32 is converted to int.";
    Int (Int32.to_int n)
  | Const_int64 n ->
    Error.warn loc "Constant of type int64 is converted to int.";
    Int (Int64.to_int n)
  | Const_nativeint n ->
    Error.warn loc "Constant of type nativeint is converted to int.";
    Int (Nativeint.to_int n)

(** Pretty-print a constant to Coq. *)
let rec to_coq (c : t) : SmartPrint.t =
  match c with
  | Int n ->
    if n >= 0 then
      OCaml.int n
    else
      parens @@ OCaml.int n
  | Nat n -> nest (to_coq (Int n) ^^ !^ "%" ^^ !^ "nat")
  | Char c ->
    let s =
      if Char.code c < 10 then
        "00" ^ string_of_int (Char.code c)
      else if Char.code c < 32 then
        "0" ^ string_of_int (Char.code c)
      else if c = '"' then
        "\"\""
      else
        String.make 1 c in
    nest (double_quotes (!^ s) ^^ !^ "%" ^^ !^ "char")
  | String s ->
    let b = Buffer.create 0 in
    s |> String.iter (fun c ->
      if c = '"' then
        Buffer.add_string b "\"\""
      else
        Buffer.add_char b c);
    nest (double_quotes (!^ (Buffer.contents b)) ^^ !^ "%" ^^ !^ "string")