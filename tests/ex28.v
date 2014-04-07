Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition map {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix map (l : list A) : list B :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map l)
    end in
  map l.

Definition map2 {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix map2 {C D : Type} (f : C -> D) (l : list C) : list D :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map2 f l)
    end in
  map2 f l.
