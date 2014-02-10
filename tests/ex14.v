Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition f (n : Z) (b : bool) : Z :=
  if b then
    (Z.add n) 1
  else
    (Z.sub n) 1.
