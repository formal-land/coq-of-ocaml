Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive tree : Set :=
| Leaf : tree
| Node : tree -> int -> tree -> tree.

Fixpoint find (x : int) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node t1 x' t2 =>
    if CoqOfOCaml.Stdlib.lt x x' then
      find x t1
    else
      if CoqOfOCaml.Stdlib.lt x' x then
        find x t2
      else
        true
  end.
