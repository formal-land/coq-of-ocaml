Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition n : Z := 12.

Definition c1 : ascii := "a" % char.

Definition c2 : ascii := "010" % char.

Definition c3 : ascii := "009" % char.

Definition c4 : ascii := """" % char.

Definition s : string := "hi
	:)""" % string.

Definition b1 : bool := false.

Definition b2 : bool := true.

Definition u : unit := tt.

Definition l1 {A : Type} : list A := [].

Definition l2 : list Z := cons 0 (cons 1 (cons 2 (cons 3 []))).

Definition o : option Z :=
  if b1 then
    None
  else
    Some n.

Definition e_match {A B : Type} (x : B) : M [ OCaml.Match_failure ] A :=
  match x with
  | _ => OCaml.raise_Match_failure (("error" % string, 1, 2))
  end.

Definition e_assert {A B : Type} (x : B) : M [ OCaml.Assert_failure ] A :=
  match x with
  | _ => OCaml.raise_Assert_failure (("error" % string, 1, 2))
  end.

Definition e_invalid {A B : Type} (x : B) : M [ OCaml.Invalid_argument ] A :=
  match x with
  | _ => OCaml.raise_Invalid_argument ("error" % string)
  end.

Definition e_failure {A B : Type} (x : B) : M [ OCaml.Failure ] A :=
  match x with
  | _ => OCaml.raise_Failure ("error" % string)
  end.

Definition e_not_found {A B : Type} (x : B) : M [ OCaml.Not_found ] A :=
  match x with
  | _ => OCaml.raise_Not_found tt
  end.

Definition e_EOF {A B : Type} (x : B) : M [ OCaml.End_of_file ] A :=
  match x with
  | _ => OCaml.raise_End_of_file tt
  end.

Definition e_div {A B : Type} (x : B) : M [ OCaml.Division_by_zero ] A :=
  match x with
  | _ => OCaml.raise_Division_by_zero tt
  end.
