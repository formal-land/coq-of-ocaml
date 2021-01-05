Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Fixpoint odd_length {A : Set} (l : list A) : bool :=
  match l with
  | [] => false
  | cons _ l => negb (even_length l)
  end

with even_length {A : Set} (l : list A) : bool :=
  match l with
  | [] => true
  | cons _ l => negb (odd_length l)
  end.
