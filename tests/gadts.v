Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive gre (a : Type) : Type :=
| Arg : a -> gre a.
Arguments Arg {a} _.

Inductive foo : forall (a b : Type), Type :=
| Bar : forall (a b c : Type), a -> Z -> b -> c -> foo b string
| Other : forall (a b : Type), Z -> foo a b.
Arguments Bar {a b c} _ _ _ _.
Arguments Other {a b} _.

Inductive expr : forall (a : Type), Type :=
| Int : expr Z
| String : expr string
| Sum : (expr Z) -> (expr Z) -> expr Z
| Pair : forall (a b : Type), (expr a) -> (expr b) -> expr (a * b).
Arguments Pair {a b} _ _.
