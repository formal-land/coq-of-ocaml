Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition u : unit := tt.

Definition l1 {A : Set} : list A := [].

Definition l2 : list Z := cons 1 [].

Definition l3 : list Z := cons 1 (cons 5 (cons 7 (cons 32 (cons 15 [])))).

Definition o1 {A : Set} : option A := None.

Definition o2 : option Z := Some 12.

Definition c : ascii := "g" % char.

Definition s1 : string := "bla" % string.

Definition s2 : string := """" % string.
