Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition r := Effect.new Z unit.

Definition read_r (_ : unit) : M [ r ] Z :=
  fun s => (inl (fst s), s).

Definition write_r (x : Z) : M [ r ] unit :=
  fun s => (inl tt, (x, tt)).
