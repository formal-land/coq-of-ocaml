Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Module List2.
  Inductive t (a : Type) : Type :=
  | Nil : t a
  | Cons : a -> (t a) -> t a.
  Arguments Nil {a} .
  Arguments Cons {a} _ _.
  
  Fixpoint sum (l : t Z) : Z :=
    match l with
    | Nil => 0
    | Cons x xs => (Z.add x) (sum xs)
    end.
  
  Fixpoint of_list {A : Type} (match_var_0 : list A) : t A :=
    match match_var_0 with
    | [] => Nil
    | cons x xs => Cons x (of_list xs)
    end.
  
  Module Inside.
    Definition x : Z := 12.
  End Inside.
End List2.

Definition n : Z :=
  List2.sum (List2.of_list (cons 5 (cons 7 (cons 6 (cons List2.Inside.x []))))).
