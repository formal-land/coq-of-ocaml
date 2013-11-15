(** Recursivity flag *)
type t =
  | Recursive
  | NonRecursive

let of_rec_flag (f : Asttypes.rec_flag) : t =
  match f with
  | Asttypes.Recursive -> Recursive
  | Asttypes.Nonrecursive -> NonRecursive
  | _ -> failwith "Recursivity flag not handled."