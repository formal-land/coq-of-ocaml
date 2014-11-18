Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

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
