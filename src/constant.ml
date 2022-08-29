open Asttypes
(** Constants. *)

open Angstrom
open SmartPrint
open Monad.Notations

(** A constant can be an integer, a natural number (used for the non-termination monad) *)
type t = Int of int | Char of char | String of string | Warn of t * string

let warn (c : t) (message : string) : t Monad.t =
  let* configuration = get_configuration in
  let with_warning = Configuration.have_constant_warning configuration in
  if with_warning then return (Warn (c, message)) else return c

(** Import an OCaml constant. *)
let of_constant (c : constant) : t Monad.t =
  match c with
  | Const_int n -> return (Int n)
  | Const_char c -> return (Char c)
  | Const_string (s, _, _) -> return (String s)
  | Const_float s ->
      let n = int_of_float (float_of_string s) in
      let message =
        Printf.sprintf "Float constant %s is approximated by the integer %d" s n
      in
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

(** Parsed string (for Coq) is
    - either a usual ocaml string with Coq printable characters
    - or a Coq non-printable character
    - or double quotes (a special case for Coq)
    https://coq.inria.fr/library/Coq.Strings.String.html
 *)
type parsed_string = PString of string | PChar of char | PDQuote

(** Kind of "good" printable characters
    (according to the coq documentation). *)
let is_printable_ascii c = Char.code c >= 32 && c <> '"'

(** Characters which may need special representation
    (according to the coq documentation), except double quotes. *)
let non_printable_ascii c = Char.code c < 32

(** Double qoutes char, special case for coq. *)
let dquote = Angstrom.map ~f:(fun _ -> PDQuote) (Angstrom.char '"')

(** Parser for Coq printable chars. *)
let printable =
  Angstrom.map
    ~f:(fun str -> PString str)
    (Angstrom.take_while1 is_printable_ascii)

(** Parser for Coq non-printable chars. *)
let nonprintable =
  Angstrom.map ~f:(fun c -> PChar c) (Angstrom.satisfy non_printable_ascii)

(** Parser for Coq string. *)
let parse_string_for_coq = many (printable <|> nonprintable <|> dquote)

(** Just a wrapper. *)
let npchar c : SmartPrint.t =
  !^"String.String" ^^ !^(Printf.sprintf "\"%03d\"" (Char.code c))

(** Pretty-print [parsed_string] to Coq. *)
let rec to_coq_s (need_parens : bool) (xs : parsed_string list) : SmartPrint.t =
  match xs with
  | [] -> double_quotes !^""
  | PChar c :: xs ->
      let res = npchar c ^^ nest @@ to_coq_s true xs in
      Pp.parens need_parens res
  | PDQuote :: xs -> to_coq_s need_parens @@ (PString "\"\"" :: xs)
  | PString s :: PDQuote :: xs ->
      to_coq_s need_parens @@ (PString (s ^ "\"\"") :: xs)
  | PString s1 :: PString s2 :: xs ->
      to_coq_s need_parens @@ (PString (s1 ^ s2) :: xs)
  | [ PString s ] -> double_quotes !^s
  | PString s :: xs ->
      Pp.parens need_parens
        (double_quotes !^s ^^ !^"++" ^^ nest @@ to_coq_s false xs)

(** Pretty-print a constant to Coq. *)
let rec to_coq (need_parens : bool) (c : t) : SmartPrint.t =
  match c with
  | Int n -> if n >= 0 then OCaml.int n else parens @@ OCaml.int n
  | Char c ->
      let s =
        if Char.code c < 32 then Printf.sprintf "%03d" (Char.code c)
        else if c = '"' then "\"\""
        else String.make 1 c
      in
      nest (double_quotes !^s ^^ !^"%" ^^ !^"char")
  | String s -> (
      match Angstrom.parse_string ~consume:All parse_string_for_coq s with
      | Result.Ok xs -> nest @@ to_coq_s need_parens xs
      | Result.Error _ ->
          (* This should mean it is an empty string
             (... or something else, but it should be a rare case). *)
          double_quotes !^"")
  | Warn (c, message) ->
      group (Error.to_comment message ^^ newline ^^ to_coq need_parens c)
