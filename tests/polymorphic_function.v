Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition f {A B : Set} (x : A) (y : B) : A := x.

Definition n : int := f 12 3.
