Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Module M.
  Definition b : bool := false.
  
  Definition n : int := 12.
End M.

Definition n : int := Z.add M.n 2.
