(** Constants. *)
open Asttypes
open SmartPrint
open Monad.Notations

(** A constant can be an integer, a natural number (used for the non-termination monad) *)
type t =
  | Int of int
  | Char of char
  | String of string
  | Warn of t * string

let warn (c : t) (message : string) : t Monad.t =
  let* configuration = get_configuration in
  let with_warning = Configuration.have_constant_warning configuration in
  if with_warning then
    return (Warn (c, message))
  else
    return c

(** Import an OCaml constant. *)
let of_constant (c : constant) : t Monad.t =
  match c with
  | Const_int n -> return (Int n)
  | Const_char c -> return (Char c)
  | Const_string (s, _, _) -> return (String (String.escaped s))
  | Const_float s ->
    let n = int_of_float (float_of_string s) in
    let message = Printf.sprintf "Float constant %s is approximated by the integer %d" s n in
    warn (Int n) message
  | Const_int32 n ->
    let message = "Constant of type int32 is converted to int" in
    warn (Int (Int32.to_int n)) message
  | Const_int64 n ->
    let message = "Constant of type int64 is converted to int" in
    warn (Int (Int64.to_int n)) message
  | Const_nativeint n ->
    let message = "Constant of type nativeint is converted to int" in
    warn (Int (Nativeint.to_int n)) message

(** Pretty-print a constant to Coq. *)
let rec to_coq (c : t) : SmartPrint.t =
  match c with
  | Int n ->
    if n >= 0 then
      OCaml.int n
    else
      parens @@ OCaml.int n
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
    double_quotes (!^ (Buffer.contents b))
  | Warn (c, message) -> group (Error.to_comment message ^^ newline ^^ to_coq c)
