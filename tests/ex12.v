Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> Z -> tree -> tree .
Arguments Leaf .
Arguments Node _ _ _.

Fixpoint find (x : Z) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node t1 x' t2 =>
    if (Z.ltb x) x' then
      (find x) t1
    else
      if (Z.ltb x') x then
        (find x) t2
      else
        true
  end.
