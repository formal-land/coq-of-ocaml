Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module List2.
  Inductive t (a : Type) : Type :=
  | Nil : t a
  | Cons : a -> (t a) -> t a.
  Arguments Nil {a}.
  Arguments Cons {a} _ _.
  
  Fixpoint sum (l : t Z) : Z :=
    match l with
    | Nil => 0
    | Cons x xs => Z.add x (sum xs)
    end.
  
  Fixpoint of_list {A : Type} (x : list A) : t A :=
    match x with
    | [] => Nil
    | cons x xs => Cons x (of_list xs)
    end.
  
  Module Inside.
    Definition x : Z := 12.
  End Inside.
End List2.

Definition n {A : Type} (x : A) : Z :=
  match x with
  | _ =>
    List2.sum
      (List2.of_list (cons 5 (cons 7 (cons 6 (cons List2.Inside.x [])))))
  end.
