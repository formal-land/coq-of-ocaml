Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition map {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix map_coq_rec (l : list A) : list B :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map_coq_rec l)
    end in
  map_coq_rec l.

Definition map2 {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix map2_coq_rec {C D : Type} (f : C -> D) (l : list C) : list D :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map2_coq_rec f l)
    end in
  map2_coq_rec f l.
