Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition op_plusplusplus (x : Z) (y : Z) : Z := Z.add x y.

Definition op_tildetilde (x : Z) : Z := Z.opp x.

Definition z : Z := op_plusplusplus (op_tildetilde 12) 14.
