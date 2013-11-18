(** Constants. *)
type t =
  | Int of int
  | Char of char
  | String of string

(** Import an OCaml constant. *)
let of_constant (c : Asttypes.constant) : t =
  let open Asttypes in
  match c with
  | Const_int n -> Int n
  | Const_char c -> Char c
  | Const_string s -> String s
  | _ -> failwith "Constant not handled."

(** Pretty-print a constant. *)
let pp (f : Format.formatter) (c : t) : unit =
  match c with
  | Int n ->
    if n >= 0 then
      Format.fprintf f "%d" n
    else
      Format.fprintf f "(%d)" n
  | Char c -> Format.fprintf f "\"%c\"@ %%@ char" c
  | String s -> Format.fprintf f "\"%s\"@ %%@ string" s
