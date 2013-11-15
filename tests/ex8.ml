(** Sum types *)
type t =
  | C1 of int
  | C2 of bool * int
  | C3

let n = C2 (false, 3)

let m = match n with
  | C2 (b, _) -> b
  | _ -> true
