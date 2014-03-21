Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive set : Type :=
| Empty : set
| Node : set -> Z -> set -> set .
Arguments Empty .
Arguments Node _ _ _.

Definition empty : set := Empty.

Fixpoint member_rec (counter : nat) (x : Z) (s : set) :
  M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret false
    | Node s1 y s2 =>
      if (Z.ltb x) y then
        ((member_rec counter) x) s1
      else
        if (Z.ltb y) x then
          ((member_rec counter) x) s2
        else
          ret true
    end
  end.

Definition member (x : Z) (s : set) : M [ Counter; NonTermination ] bool :=
  let! x_1 :=
    lift [_;_] "10"
      (let! x_1 :=
        let! x_1 := read_counter tt in
        ret (member_rec x_1) in
      ret (x_1 x)) in
  lift [_;_] "01" (x_1 s).

Fixpoint insert_rec (counter : nat) (x : Z) (s : set) : M [ NonTermination ] set
  :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match s with
    | Empty => ret (Node Empty x Empty)
    | Node s1 y s2 =>
      if (Z.ltb x) y then
        let! x_1 := ((insert_rec counter) x) s1 in
        ret (Node x_1 y s2)
      else
        if (Z.ltb y) x then
          let! x_1 := ((insert_rec counter) x) s2 in
          ret (Node s1 y x_1)
        else
          ret s
    end
  end.

Definition insert (x : Z) (s : set) : M [ Counter; NonTermination ] set :=
  let! x_1 :=
    lift [_;_] "10"
      (let! x_1 :=
        let! x_1 := read_counter tt in
        ret (insert_rec x_1) in
      ret (x_1 x)) in
  lift [_;_] "01" (x_1 s).
