Require Import Coq.Program.Equality.

Inductive unit_or_double_unit : Set -> Set :=
| Unit : unit_or_double_unit unit
| Double_unit : unit_or_double_unit (unit * unit).

(* let twelve (x : unit unit_or_double_unit) = *)
(* match x with *)
(* | Unit -> 12 *)

Axiom H: (prod unit unit <> unit).
Hint Resolve H.

Program Definition twelve (x: unit_or_double_unit unit) : nat :=
  match x
        as y
        in unit_or_double_unit z
        return z = unit -> nat
  with
  | Unit => fun H => 12
  | Double_unit => fun Heq => _
                    (* False_rect nat *)
  end _.
Next Obligation.
  apply False_rect.
  auto.
Defined.

Inductive t : list Set -> Set -> Type :=
| k : t (nat :: bool :: nil) (nat * bool).

From Equations Require Import Equations.

Equations twelve (x : unit_or_double_unit unit): nat :=
  twelve Unit := 12.


From Antivalence Require Import Loader.

Require Import Antivalence.Loader.

Definition foo : forall A B (p: t (A :: B :: nil) (A * B)) (x: A), nat :=
  fun A B p x y =>
  match p in t T' T return T -> nat with
  | k => fun v => v
  end (x).


Inductive t : Type -> Type :=
| k : t (nat * bool).

Definition foo : forall A B (p: t (A * B)) (x: A) (y: B), nat :=
  fun A B p x y =>
  match p in t T return forall T1 T2, T = prod T1 T2 -> T1 -> nat with
  | k => fun _ _ _ v => v
  end (x).
Next Obligation.
  inversion Heq_anonymous.
  inversion H2.
  dependent destruction p.
  destruct dependent
  intros.
  inversion p.
 o
