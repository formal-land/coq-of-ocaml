Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> Z -> tree -> tree .
Arguments Leaf .
Arguments Node _ _ _.

Fixpoint find_rec (counter : nat) (x : Z) (t : tree) :
  M [ Err_NonTermination ] bool :=
  match counter with
  | 0 % nat => not_terminated tt
  | S counter =>
    match t with
    | Leaf => ret false
    | Node t1 x' t2 =>
      if (Z.ltb x) x' then
        ((find_rec counter) x) t1
      else
        if (Z.ltb x') x then
          ((find_rec counter) x) t2
        else
          ret true
    end
  end.

Definition find (x : Z) (t : tree) : M [ Ref_Counter; Err_NonTermination ] bool
  :=
  let! counter := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (((find_rec counter) x) t).
