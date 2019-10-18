Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive gre (a : Type) : Type :=
| Arg : a -> gre a.

Arguments Arg {_}.

Inductive foo : forall (a b : Type), Type :=
| Bar : forall {a b c : Type}, a -> Z -> b -> c -> foo b string
| Other : forall {a b : Type}, Z -> foo a b.

Inductive expr : forall (a : Type), Type :=
| Int : Z -> expr Z
| String : string -> expr string
| Sum : (expr Z) -> (expr Z) -> expr Z
| Pair : forall {a b : Type}, (expr a) -> (expr b) -> expr (a * b).

Fixpoint proj_int (e : expr Z) : Z :=
  match e with
  | Int n => n
  | Sum e1 e2 => Z.add (proj_int e1) (proj_int e2)
  | _ => 0
  end.
