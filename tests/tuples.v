Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition t0 : unit := tt.

Definition t1 : ascii * string := ("c" % char, "one").

Definition t2 : int * int * int * bool * bool := (1, 2, 3, false, true).

Definition f {A : Set} (x : A) : A * A := (x, x).

Definition t3 : int * int := f 12.
