Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition op_plusplusplus (x : int) (y : int) : int := Z.add x y.

Definition op_tildetilde (x : int) : int := Z.opp x.

Definition z : int := op_plusplusplus (op_tildetilde 12) 14.
