Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition foo := string.

Inductive tree (a : Type) : Type :=
| Tree : (list (node a)) -> tree a

with node (a : Type) : Type :=
| Leaf : string -> node a
| Node : (tree a) -> node a

with unrelated (a : Type) : Type :=
| Unrelated : a -> a -> unrelated a.
Arguments Tree {a} _.
Arguments Leaf {a} _.
Arguments Node {a} _.
Arguments Unrelated {a} _ _.
