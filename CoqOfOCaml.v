Require Export ZArith.
Require Export Ascii.
Require Export String.
Require Export List.
Require Export Program.Basics.
Require Export Classes.SetoidDec.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition reverse_apply {A B : Type} (x : A) (f : A -> B) : B :=
  f x.

Definition int_of_char (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Definition char_of_int (n : Z) : ascii :=
  ascii_of_nat (Z.to_nat n).

Definition ignore {A : Type} (_ : A) : unit :=
  tt.

(** The concatenation of lists with an implicit parameter. *)
Definition app {A : Type} (l1 l2 : list A) : list A :=
  app l1 l2.

Definition M (A : Type) : Type :=
  A.

Definition ret {A : Type} (x : A) : A :=
  x.

Definition bind {A B : Type} (x : A) (f : A -> B) : B :=
  f x.

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).