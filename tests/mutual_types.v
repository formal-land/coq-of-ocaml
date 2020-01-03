Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition foo := string.

Reserved Notation "'simple".
Reserved Notation "'double".

Inductive tree (a : Type) : Type :=
| Tree : list (node a) -> tree a

with node (a : Type) : Type :=
| Leaf : string -> node a
| Node : tree a -> node a

with unrelated (a : Type) : Type :=
| Unrelated : 'double ('simple a) -> unrelated a

where "'simple" := (fun (b : Type) => b)
and "'double" := (fun (b : Type) => b * 'simple b).

Definition simple := 'simple.
Definition double := 'double.

Arguments Tree {_}.
Arguments Leaf {_}.
Arguments Node {_}.
Arguments Unrelated {_}.

Reserved Notation "'re".
Reserved Notation "'re_bis".

Record re_bis_skeleton {bis : Type} := {
  bis : bis }.
Arguments re_bis_skeleton : clear implicits.

Record re_skeleton {payload message : Type} := {
  payload : payload;
  message : message }.
Arguments re_skeleton : clear implicits.

Inductive ind : Type :=
| Ind : 're Z -> ind

where "'re" := (fun (a : Type) => re_skeleton a string)
and "'re_bis" := (re_bis_skeleton unit).

Definition re := 're.
Definition re_bis := 're_bis.
