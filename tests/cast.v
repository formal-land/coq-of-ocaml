Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Definition f (x : int) : int := Z.add (cast int x) 1.

Inductive t : Set :=
| Int : t.

Definition g {a : Set} (kind : t) (x : a) : int :=
  let 'Int := kind in
  Z.add (cast int x) 1.
