Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition f (n : int) (b : bool) : int :=
  if b then
    Z.add n 1
  else
    Z.sub n 1.

Definition id {a : Set} (x : a) : a := x.
