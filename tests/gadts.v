Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive gre : forall (a : Type), Type :=
| Arg : forall {a : Type}, a -> gre a.

Inductive foo : forall (a b : Type), Type :=
| Bar : forall {a b c : Type}, a -> Z -> b -> c -> foo b string
| Other : forall {a b : Type}, Z -> foo a b.

Inductive expr : forall (a : Type), Type :=
| Int : expr Z
| String : expr string
| Sum : (expr Z) -> (expr Z) -> expr Z
| Pair : forall {a b : Type}, (expr a) -> (expr b) -> expr (a * b).
