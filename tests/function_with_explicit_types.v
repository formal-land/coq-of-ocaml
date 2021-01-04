Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Definition f (n : int) (b : bool) : int :=
  if b then
    Z.add n 1
  else
    Z.sub n 1.

Definition id {a : Set} (x : a) : a := x.
