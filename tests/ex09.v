Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l : list Z :=
  let fix map {A B : Type} (f : B -> A) (match_var_0 : list B) : list A :=
    match match_var_0 with
    | [] => []
    | cons x xs => cons (f x) ((map f) xs)
    end in
  (map (fun n => (Z.add n) 1)) (cons 5 (cons 7 (cons 8 []))).
