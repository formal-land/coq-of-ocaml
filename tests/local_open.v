Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Module Notations.
  Definition keep_same {A : Set} (x : A) : A := x.
  
  Definition op_plus (s1 : string) (s2 : string) : string :=
    String.append s1 s2.
End Notations.

Definition concat (s1 : string) (s2 : string) : string :=
  Notations.keep_same (Notations.op_plus s1 s2).
