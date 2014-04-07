Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint f_map_rec {A B : Type} (counter : nat) (f : B -> A) (l : list B) :
  M [ NonTermination ] (list A) :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret []
    | cons x l =>
      let! x_1 := (f_map_rec counter) f l in
      ret (cons (f x) x_1)
    end
  end.

Definition f_map {A B : Type} (f : B -> A) (l : list B) :
  M [ Counter; NonTermination ] (list A) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (f_map_rec x f l).

Fixpoint f_map2_rec {A B : Type} (counter : nat) (f : B -> A) (l : list B) :
  M [ NonTermination ] (list A) :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret []
    | cons x l =>
      let! x_1 := (f_map2_rec counter) f l in
      ret (cons (f x) x_1)
    end
  end.

Definition f_map2 {A B : Type} (f : B -> A) (l : list B) :
  M [ Counter; NonTermination ] (list A) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (f_map2_rec x f l).
