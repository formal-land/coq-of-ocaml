Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Module M.
  Definition n : int := 12.
End M.

Module N.
  Definition n : bool := true.
  
  Definition x : bool := n.
  
  Definition y : int := M.n.
End N.

Definition b : bool := N.n.

Definition b' : bool := N.n.
