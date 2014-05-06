Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive tree : Type :=
| Leaf : tree
| Node : tree -> Z -> tree -> tree .
Arguments Leaf .
Arguments Node _ _ _.

Fixpoint find_rec (counter : nat) (x : Z) (t : tree)
  : M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match t with
    | Leaf => ret false
    | Node t1 x' t2 =>
      if OCaml.Pervasives.lt x x' then
        (find_rec counter) x t1
      else
        if OCaml.Pervasives.lt x' x then
          (find_rec counter) x t2
        else
          ret true
    end
  end.

Definition find (x : Z) (t : tree) : M [ Counter; NonTermination ] bool :=
  let! x_1 := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (find_rec x_1 x t).
