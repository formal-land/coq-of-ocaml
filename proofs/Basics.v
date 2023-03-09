Require Import ssr.ssrbool.
Require Import Libraries.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive sigS (A : Type) (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

(** Conversion from a module to a first-class module. *)
Definition pack {A : Type} {P : A -> Set} (M : {x : A & P x}) : {x : A @ P x} :=
  let 'existT _ _ M := M in
  existS _ _ M.

Notation "(| record |)" := (projT2 record).

Module Primitive.
  Set Primitive Projections.

  Record prod {A B : Type} : Type := pair {
    fst : A;
    snd : B;
  }.
  Arguments prod : clear implicits.

  Unset Primitive Projections.
End Primitive.

Notation "[ X ** Y ** .. ** Z ]" :=
  (Primitive.prod .. (Primitive.prod X Y) .. Z) : type_scope.
Notation "[ x , y , .. , z ]" :=
  (Primitive.pair .. (Primitive.pair x y) .. z).

Definition array (A : Set) : Set := list A.

Parameter axiom : forall {A : Set}, A.

Parameter assert : forall (A : Set), bool -> A.

Axiom cast : forall {A : Set} (B : Set), A -> B.

Axiom cast_exists : forall {A : Set} {Es : Type} (T : Es -> Set),
  A -> {vs : Es & T vs}.

Axiom cast_eval : forall {A : Set} {x : A}, cast A x = x.

Axiom cast_exists_eval_eq
  : forall {A : Set} {Es : Type} {T : Es -> Set} {vs : Es} {x : A}
  (H_eq : A = T vs),
  cast_exists (A := A) (Es := Es) T x =
  existT T vs (eq_rect (A := Set) A (fun x => x) x (T vs) H_eq).

Ltac rewrite_cast_exists_eval_eq vs :=
  match goal with
  | [ |- context[cast_exists ?T _] ] =>
    rewrite (cast_exists_eval_eq (T := T) (vs := vs) eq_refl);
    simpl
  end.

Parameter unreachable_gadt_branch : forall {A : Set}, A.

Parameter unreachable : forall {A : Set}, A.

(** Mutation of a record field. *)
Parameter set_record_field : forall {A B : Set}, A -> string -> B -> unit.

Inductive extensible_type : Set :=
| Build_extensible : string -> forall (A : Set), A -> extensible_type.
Arguments Build_extensible : clear implicits.

(** For backward compatibility. *)
Parameter extensible_type_value : extensible_type.

(** Polymorphic variants. *)
Module Variant.
  Inductive t : Set :=
  | Build : string -> forall (A : Set), A -> t.

  Arguments Build : clear implicits.
End Variant.

Parameter Set_oracle : string -> Set.

Axiom Set_oracle_invoke
  : forall {name : string} (A : Set),
    Set_oracle name = A.

Definition exn : Set := extensible_type.

Definition int := Z.

Definition float := Z.

Definition int32 := Z.

Definition int64 := Z.

Definition nativeint := Z.

Definition char := ascii.

Definition bytes := string.

Definition try {A : Set} (x : A) : A := x.

Definition try_with {A : Set} (e : unit -> A) (_with : extensible_type -> A)
  : A :=
  e tt.
