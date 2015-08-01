Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Fixpoint f_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | cons x l => cons (f x) (f_map f l)
  end.

Fixpoint f_map2_rec {A B : Type} (counter : nat) (f : A -> B) (l : list A)
  : M [ NonTermination ] (list B) :=
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

Definition f_map2 {A B : Type} (f : A -> B) (l : list A)
  : M [ Counter; NonTermination ] (list B) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (f_map2_rec x f l).

Definition n : Z :=
  let fix sum_coq_rec (l : list Z) : Z :=
    match l with
    | [] => 0
    | cons x l => Z.add x (sum_coq_rec l)
    end in
  sum_coq_rec (cons 1 (cons 2 (cons 3 []))).

Definition n2 {A : Type} (x : A) : M [ Counter; NonTermination ] Z :=
  match x with
  | _ =>
    let fix sum_rec (counter : nat) (l : list Z) : M [ NonTermination ] Z :=
      match counter with
      | O => not_terminated tt
      | S counter =>
        match l with
        | [] => ret 0
        | cons x l =>
          let! x_1 := (sum_rec counter) l in
          ret (Z.add x x_1)
        end
      end in
    let sum (l : list Z) : M [ Counter; NonTermination ] Z :=
      let! x_1 := lift [_;_] "10" (read_counter tt) in
      lift [_;_] "01" (sum_rec x_1 l) in
    sum (cons 1 (cons 2 (cons 3 [])))
  end.
