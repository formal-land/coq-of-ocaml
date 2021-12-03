Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition op_plusplusplus (x_value : int) (y_value : int) : int :=
  Z.add x_value y_value.

Definition op_tildetilde (x_value : int) : int := Z.opp x_value.

Definition z_value : int := op_plusplusplus (op_tildetilde 12) 14.
