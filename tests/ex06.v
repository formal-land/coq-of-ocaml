Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint map {A B : Type} (f : B -> A) (l : list B) : list A :=
  match l with
  | [] => []
  | cons x xs => cons (f x) ((map f) xs)
  end.

Fixpoint fold {A B : Type} (f : A -> B -> A) (a : A) (l : list B) : A :=
  match l with
  | [] => a
  | cons x xs => ((fold f) ((f a) x)) xs
  end.

Definition l : list Z := cons 5 (cons 6 (cons 7 (cons 2 []))).

Definition n {A : Type} (incr : Z -> A) (plus : Z -> A -> Z) : Z :=
  ((fold (fun x => fun y => (plus x) y)) 0) ((map incr) l).
