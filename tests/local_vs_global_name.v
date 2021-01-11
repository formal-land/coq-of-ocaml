Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module M.
  Definition b : bool := false.
  
  Definition n : int := 12.
End M.

Definition n : int := Z.add M.n 2.
