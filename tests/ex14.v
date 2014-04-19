Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Import ListNotations.

Definition f (n : Z) (b : bool) : Z :=
  if b then
    Z.add n 1
  else
    Z.sub n 1.
