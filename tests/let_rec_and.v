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

Definition local_let_and_variables (x : int) : int :=
  let y : int :=
    12
  in let z : int :=
    Z.mul 2 x in
  Z.add y z.
