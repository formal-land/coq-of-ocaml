Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Fixpoint odd_length {A : Set} (l_value : list A) : bool :=
  match l_value with
  | [] => false
  | cons _ l_value => negb (even_length l_value)
  end

with even_length {A : Set} (l_value : list A) : bool :=
  match l_value with
  | [] => true
  | cons _ l_value => negb (odd_length l_value)
  end.

Definition local_let_and_variables (x_value : int) : int :=
  let y_value : int :=
    12
  in let z_value : int :=
    Z.mul 2 x_value in
  Z.add y_value z_value.
