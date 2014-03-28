Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition e_invalid {A B : Type} (x : B) : M [ OCaml.Invalid_argument ] A :=
  match x with
  | _ => OCaml.Pervasives.invalid_arg "error" % string
  end.

Definition e_failure {A B : Type} (x : B) : M [ OCaml.Failure ] A :=
  match x with
  | _ => OCaml.Pervasives.failwith "error" % string
  end.

Definition e_exit1 {A B : Type} (x : B) : M [ OCaml.Pervasives.Exit ] A :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.

Definition e_exit2 {A B : Type} (x : B) : M [ OCaml.Pervasives.Exit ] A :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.
