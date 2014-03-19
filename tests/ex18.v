Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition r := Effect.make Z unit.

Definition read_r (_ : unit) : M [ r ] Z :=
  fun s => (inl (fst s), s).

Definition write_r (x : Z) : M [ r ] unit :=
  fun s => (inl tt, (x, tt)).

Definition plus_one {A : Type} (x : A) : M [ r ] Z :=
  match x with
  | _ =>
    let! x :=
      let! x := read_r tt in
      ret (Z.add x) in
    ret (x 1)
  end.

Definition s := Effect.make string unit.

Definition read_s (_ : unit) : M [ s ] string :=
  fun s => (inl (fst s), s).

Definition write_s (x : string) : M [ s ] unit :=
  fun s => (inl tt, (x, tt)).

Definition fail {A B : Type} (x : B) : M [ s; Failure ] A :=
  match x with
  | _ =>
    let! x := lift [_;_] "10" (read_s tt) in
    lift [_;_] "01" (failwith x)
  end.

Definition reset {A : Type} (x : A) : M [ r ] unit :=
  match x with
  | _ => write_r 0
  end.

Definition incr {A : Type} (x : A) : M [ r ] unit :=
  match x with
  | _ =>
    let! x :=
      let! x :=
        let! x := read_r tt in
        ret (Z.add x) in
      ret (x 1) in
    write_r x
  end.