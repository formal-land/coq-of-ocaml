(** Matching *)

let n = match ([1; 2], false) with
  | ([x; _], true) -> x
  | ([_; y], false) -> y
  | _ -> 0
