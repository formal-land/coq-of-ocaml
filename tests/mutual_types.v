Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition foo := string.

Inductive tree : forall (a : Type), Type :=
| Tree : forall {a : Type}, (list (node a)) -> tree a

with node : forall (a : Type), Type :=
| Leaf : forall {a : Type}, string -> node a
| Node : forall {a : Type}, (tree a) -> node a

with unrelated : forall (a : Type), Type :=
| Unrelated : forall {a : Type}, a -> a -> unrelated a.
