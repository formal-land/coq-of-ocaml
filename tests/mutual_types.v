Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition foo := string.

Reserved Notation "'simple".
Reserved Notation "'double".

Inductive tree (a : Set) : Set :=
| Tree : list (node a) -> tree a

with node (a : Set) : Set :=
| Leaf : string -> node a
| Node : tree a -> node a

with unrelated (a : Set) : Set :=
| Unrelated : 'double ('simple a) -> unrelated a

where "'simple" := (fun (b : Set) => b)
and "'double" := (fun (b : Set) => b * 'simple b).

Definition simple := 'simple.
Definition double := 'double.

Arguments Tree {_}.
Arguments Leaf {_}.
Arguments Node {_}.
Arguments Unrelated {_}.

Reserved Notation "'re".
Reserved Notation "'re_bis".

Record re_bis_skeleton {bis : Set} := {
  bis : bis }.
Arguments re_bis_skeleton : clear implicits.

Record re_skeleton {payload message : Set} := {
  payload : payload;
  message : message }.
Arguments re_skeleton : clear implicits.

Inductive ind : Set :=
| Ind : 're Z -> ind

where "'re" := (fun (a : Set) => re_skeleton a string)
and "'re_bis" := (re_bis_skeleton unit).

Definition re := 're.
Definition re_bis := 're_bis.
