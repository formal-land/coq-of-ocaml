Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition map {A711 A716 : Type} (f : A716 -> A711) (l : list A716) : list A711
  :=
  let fix map (l : list A716) : list A711 :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map l)
    end in
  map l.

Definition map2 {A792 A794 : Type} (f : A794 -> A792) (l : list A794) :
  list A792 :=
  let fix map2 {A769 A774 : Type} (f : A774 -> A769) (l : list A774) : list A769
    :=
    match l with
    | [] => []
    | cons x l => cons (f x) (map2 f l)
    end in
  map2 f l.
