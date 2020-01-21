let n = match ([1; 2], false) with
  | ([x; _], true) -> x
  | ([_; y], false) -> y
  | _ -> 0

type t = Bar of int | Foo of bool * string

let m x =
  match x with
  | Bar n when n > 12 -> n
  | Bar k when k = 0 -> k
  | Bar n -> -n
  | Foo _ -> 0
