Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition foo := string.

Reserved Notation "'simple".
Reserved Notation "'double".

Inductive tree (a : Type) : Type :=
| Tree : (list (node a)) -> tree a

with node (a : Type) : Type :=
| Leaf : string -> node a
| Node : (tree a) -> node a

with unrelated (a : Type) : Type :=
| Unrelated : ('double ('simple a)) -> unrelated a

where "'simple" := (fun (b : Type) => b)

and "'double" := (fun (b : Type) => b * ('simple b)).

Definition simple := 'simple.
Definition double := 'double.

Arguments Tree {_}.
Arguments Leaf {_}.
Arguments Node {_}.
Arguments Unrelated {_}.
