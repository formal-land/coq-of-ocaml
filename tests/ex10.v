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
  
  Fixpoint sum_rec (counter : nat) (l : t Z) : M [ NonTermination ] Z :=
    match counter with
    | O => not_terminated tt
    | S counter =>
      match l with
      | Nil => ret 0
      | Cons x xs =>
        let! x_1 := (sum_rec counter) xs in
        ret ((Z.add x) x_1)
      end
    end.
  
  Definition sum (l : t Z) : M [ Counter; NonTermination ] Z :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" ((sum_rec counter) l).
  
  Fixpoint of_list_rec {A : Type} (counter : nat) (x : list A) :
    M [ NonTermination ] (t A) :=
    match counter with
    | O => not_terminated tt
    | S counter =>
      match x with
      | [] => ret Nil
      | cons x xs =>
        let! x_1 := (of_list_rec counter) xs in
        ret (Cons x x_1)
      end
    end.
  
  Definition of_list {A : Type} (x : list A) :
    M [ Counter; NonTermination ] (t A) :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" ((of_list_rec counter) x).
  
  Module Inside.
    Definition x : Z := 12.
  End Inside.
End List2.

Definition n {A : Type} (x : A) : M [ Counter; NonTermination ] Z :=
  match x with
  | _ =>
    let! x := List2.of_list (cons 5 (cons 7 (cons 6 (cons List2.Inside.x []))))
      in
    List2.sum x
  end.
