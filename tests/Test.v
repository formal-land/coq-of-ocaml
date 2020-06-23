(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive foo : Set :=
| FooC : bar -> foo
| FooC2 : forall (A: Set), A -> foo

with bar : Set :=
| BarC : bar.

Require Import Coq.Program.Equality.

Inductive foo_wf : foo -> Set -> Prop :=
| FooC_wf : forall (b: bar), foo_wf (FooC b) bar
| FooC2_wf: forall (A: Set) (a: A), foo_wf (FooC2 A a) A
.

Definition foo' (f: foo) := { t | foo_wf f t }.

Definition foo_wf' (f : foo) (t : Set) : Prop :=
  match f return Prop with
  | FooC _ => t = bar
  | FooC2 A _ => A ~= t
  end.

Section tS.
  Polymorphic Universe i.

  Polymorphic Inductive t : Type@{i+1} :=
  | Nil : t
  | Cons : forall {a : Type@{i}}, a -> t -> t.

  Polymorphic Fixpoint of_list {A : Type@{i}} (l : list A) : t :=
    match l with
    | nil => Nil
    | @cons _ a l => Cons (of_list l) (of_list l)
    end.

Eval compute in of_list [1;5].
