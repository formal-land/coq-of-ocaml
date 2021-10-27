(** Recursivity flag. *)

type t = bool

(** Import an OCaml recursivity flag. *)
let of_rec_flag (f : Asttypes.rec_flag) : t =
  match f with Asttypes.Recursive -> true | Asttypes.Nonrecursive -> false
