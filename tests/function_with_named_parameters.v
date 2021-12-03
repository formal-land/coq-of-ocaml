Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition option_value {a : Set} (x_value : option a) (default : a) : a :=
  match x_value with
  | Some x_value => x_value
  | None => default
  end.

Definition option_zero : option int -> int := fun x_1 => option_value x_1 0.

Definition option_value_bis {A : Set} : option A -> A -> A := option_value.
