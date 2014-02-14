(** Unbalanced set from CFML. *)

type set =
  | Empty
  | Node of set * int * set

let empty = Empty

let rec member x s =
  match s with
  | Empty -> false
  | Node (s1, y, s2) -> 
    if x < y then
      member x s1
    else if y < x then
      member x s2
    else
      true

let rec insert x s =
  match s with
  | Empty -> Node (Empty, x, Empty)
  | Node (s1, y, s2) ->
    if x < y then
      Node (insert x s1, y, s2)
    else if y < x then
      Node (s1, y, insert x s2)
    else s