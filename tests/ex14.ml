(** Function declaration with explicit argument types *)

let f (n : int) (b : bool) =
  if b then
    n + 1
  else
    n - 1