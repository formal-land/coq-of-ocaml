Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition map {A B : Set} (f_value : A -> B) (l_value : list A) : list B :=
  let fix map_coq_rec (l_value : list A) : list B :=
    match l_value with
    | [] => nil
    | cons x_value l_value => cons (f_value x_value) (map_coq_rec l_value)
    end in
  map_coq_rec l_value.

Definition map2 {A B : Set} (f_value : A -> B) (l_value : list A) : list B :=
  let fix map2_coq_rec {C D : Set} (f_value : C -> D) (l_value : list C)
    : list D :=
    match l_value with
    | [] => nil
    | cons x_value l_value =>
      cons (f_value x_value) (map2_coq_rec f_value l_value)
    end in
  map2_coq_rec f_value l_value.
