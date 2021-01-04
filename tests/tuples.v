Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Definition t0 : unit := tt.

Definition t1 : ascii * string := ("c" % char, "one").

Definition t2 : int * int * int * bool * bool := (1, 2, 3, false, true).

Definition f {A : Set} (x : A) : A * A := (x, x).

Definition t3 : int * int := f 12.
