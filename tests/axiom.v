Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Axiom show : forall {a : Set}, a -> string.

Axiom recursive : forall {a : Set}, a -> string.
