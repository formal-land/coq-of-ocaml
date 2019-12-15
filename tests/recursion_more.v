Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Fixpoint f_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | cons x l => cons (f x) (f_map f l)
  end.

Definition n : Z :=
  let fix sum (l : list Z) : Z :=
    match l with
    | [] => 0
    | cons x l => Z.add x (sum l)
    end in
  sum (cons 1 (cons 2 (cons 3 []))).
