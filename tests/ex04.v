Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition u : unit := tt.

Definition l1 {A : Type} : list A := [].

Definition l2 : list Z := cons 1 [].

Definition l3 : list Z := cons 1 (cons 5 (cons 7 (cons 32 (cons 15 [])))).

Definition o1 {A : Type} : option A := None.

Definition o2 : option Z := Some 12.

Definition c : ascii := "g" % char.

Definition s1 : string := "bla" % string.

Definition s2 : string := """" % string.
