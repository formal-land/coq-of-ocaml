(** Unbalanced set *)

type tree =
  | Leaf
  | Node of tree * int * tree

let rec find x t =
  match t with
  | Leaf -> false
  | Node (t1, x', t2) ->
    if x < x' then
      find x t1
    else if x' < x then
      find x t2
    else
      true
