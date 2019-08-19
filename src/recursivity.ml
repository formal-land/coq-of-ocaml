(** Recursivity flag. *)
open Sexplib.Std
open SmartPrint

type t = New of bool
  [@@deriving sexp]

(** Import an OCaml recursivity flag. *)
let of_rec_flag (f : Asttypes.rec_flag) : t =
  match f with
  | Asttypes.Recursive -> New true
  | Asttypes.Nonrecursive -> New false

let to_bool (r : t) : bool =
  match r with
  | New b -> b
