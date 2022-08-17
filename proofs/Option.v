Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require CoqOfOCaml.Seq.

Definition t {a : Set}:= option a.

Inductive result (a b : Set) : Set :=
| Ok : a -> result a b
| Error : b -> result a b.


Parameter none : forall {a : Set}, option a.

Parameter some : forall {a : Set}, a -> option a.

Parameter value : forall {a : Set}, option a -> a.

Parameter get : forall {a : Set}, option a -> a.

Parameter bind : forall {a b : Set}, option a -> (a -> option b) -> option b.

Parameter join : forall {a : Set}, option (option a) -> option a.

Parameter map : forall {a b : Set}, (a -> b) -> option a -> option b.

Parameter fold : forall {a b : Set}, (b -> a) -> option b -> a.

Parameter iter : forall {a : Set}, (a -> unit) -> option a -> unit.

(** Predicates and comparisons **)
Parameter is_none : forall {a : Set}, option a -> bool.

Parameter is_some : forall {a : Set}, option a -> bool.

Parameter equal : forall {a : Set}, (a -> a -> bool) -> option a -> option a -> bool.

Parameter compare : forall {a : Set}, (a -> a -> int) -> option a -> option a -> int.

(** Converting **)
Parameter to_result : forall {a e : Set}, e -> option a -> result a e.

Parameter to_list : forall {a : Set}, option a -> list a.

Parameter to_seq : forall {a : Set}, option a -> Seq.t a.
