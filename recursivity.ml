(** Recursivity flag. *)
type t =
  | Recursive
  | NonRecursive

(** Import an OCaml recursivity flag. *)
let of_rec_flag (f : Asttypes.rec_flag) : t =
  match f with
  | Asttypes.Recursive -> Recursive
  | Asttypes.Nonrecursive -> NonRecursive
  | Asttypes.Default -> failwith "Recursivity flag not handled."