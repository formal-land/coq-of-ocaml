Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Fixpoint map {A B : Set} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Fixpoint fold {A B : Set} (f : A -> B -> A) (a : A) (l : list B) : A :=
  match l with
  | [] => a
  | cons x xs => fold f (f a x) xs
  end.

Definition l : list int := [ 5; 6; 7; 2 ].

Definition n {A : Set} (incr : int -> A) (plus : int -> A -> int) : int :=
  fold (fun (x : int) => fun (y : A) => plus x y) 0 (map incr l).
