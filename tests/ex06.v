Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint map_rec {A B : Type} (counter : nat) (f : B -> A) (l : list B) :
  M [ NonTermination ] (list A) :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret []
    | cons x xs =>
      let! x_1 := ((map_rec counter) f) xs in
      ret (cons (f x) x_1)
    end
  end.

Definition map {A B : Type} (f : B -> A) (l : list B) :
  M [ Counter; NonTermination ] (list A) :=
  let! counter := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (((map_rec counter) f) l).

Fixpoint fold_rec {A B : Type}
  (counter : nat) (f : A -> B -> A) (a : A) (l : list B) :
  M [ NonTermination ] A :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret a
    | cons x xs => (((fold_rec counter) f) ((f a) x)) xs
    end
  end.

Definition fold {A B : Type} (f : A -> B -> A) (a : A) (l : list B) :
  M [ Counter; NonTermination ] A :=
  let! counter := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" ((((fold_rec counter) f) a) l).

Definition l : list Z := cons 5 (cons 6 (cons 7 (cons 2 []))).

Definition n {A : Type} (incr : Z -> A) (plus : Z -> A -> Z) :
  M [ Counter; NonTermination ] Z :=
  let! x := (map incr) l in
  ((fold (fun x => fun y => (plus x) y)) 0) x.
