Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive set : Type :=
| Empty : set
| Node : set -> Z -> set -> set .
Arguments Empty .
Arguments Node _ _ _.

Definition empty : set := Empty.

Fixpoint member_rec (counter : nat) (x : Z) (s : set)
  : M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret false
    | Node s1 y s2 =>
      if OCaml.Pervasives.lt x y then
        (member_rec counter) x s1
      else
        if OCaml.Pervasives.lt y x then
          (member_rec counter) x s2
        else
          ret true
    end
  end.

Definition member (x : Z) (s : set) : M [ Counter; NonTermination ] bool :=
  let! x_1 := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (member_rec x_1 x s).

Fixpoint insert_rec (counter : nat) (x : Z) (s : set)
  : M [ NonTermination ] set :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret (Node Empty x Empty)
    | Node s1 y s2 =>
      if OCaml.Pervasives.lt x y then
        let! x_1 := (insert_rec counter) x s1 in
        ret (Node x_1 y s2)
      else
        if OCaml.Pervasives.lt y x then
          let! x_1 := (insert_rec counter) x s2 in
          ret (Node s1 y x_1)
        else
          ret s
    end
  end.

Definition insert (x : Z) (s : set) : M [ Counter; NonTermination ] set :=
  let! x_1 := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (insert_rec x_1 x s).
