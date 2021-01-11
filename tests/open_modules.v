Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module M.
  Definition n : int := 12.
End M.

Module N.
  Definition n : bool := true.
  
  Definition x : bool := n.
  
  Definition y : int := M.n.
End N.

Definition b : bool := N.n.

Definition b' : bool := N.n.
