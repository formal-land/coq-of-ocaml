let f x =
  x[@coq_cast] + 1

type _ t =
  | Int : int t

let g (type a) (kind : a t) (x : a) : int =
  match kind with
  | Int -> (x[@coq_cast] : int) + 1
