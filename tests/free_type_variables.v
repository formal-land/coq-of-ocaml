Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition map {A B : Set} (f : A -> B) (l : list A) : list B :=
  let fix map_coq_rec (l : list A) : list B :=
    match l with
    | [] => nil
    | cons x l => cons (f x) (map_coq_rec l)
    end in
  map_coq_rec l.

Definition map2 {A B : Set} (f : A -> B) (l : list A) : list B :=
  let fix map2_coq_rec {C D : Set} (f : C -> D) (l : list C) : list D :=
    match l with
    | [] => nil
    | cons x l => cons (f x) (map2_coq_rec f l)
    end in
  map2_coq_rec f l.
