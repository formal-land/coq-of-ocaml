Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition f {A B : Type} (x : A) (y : B) : A := x.

Definition n : Z := f 12 3.
