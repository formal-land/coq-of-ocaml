Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module List2.
  Inductive t : forall (a : Type), Type :=
  | Nil : forall {a : Type}, t a
  | Cons : forall {a : Type}, a -> (t a) -> t a.
  
  Fixpoint sum (l : t Z) : Z :=
    match l with
    | Nil => 0
    | Cons x xs => Z.add x (sum xs)
    end.
  
  Fixpoint of_list {A : Type} (function_parameter : list A) : t A :=
    match function_parameter with
    | [] => Nil
    | cons x xs => Cons x (of_list xs)
    end.
  
  Module Inside.
    Definition x : Z := 12.
  End Inside.
End List2.

Definition n {A : Type} (function_parameter : A) : Z :=
  match function_parameter with
  | _ =>
    List2.sum
      (List2.of_list (cons 5 (cons 7 (cons 6 (cons List2.Inside.x [])))))
  end.
