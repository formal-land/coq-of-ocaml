Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Import ListNotations.

Module M.
  Definition b : bool := false.
  
  Definition n : Z := 12.
End M.

Definition n : Z := Z.add M.n 2.
