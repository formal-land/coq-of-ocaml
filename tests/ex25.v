Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l1 : list Z := [].

Definition l2 : list Z := cons 1 (cons 2 (cons 3 [])).

Definition s1 : Z := OCaml.List.length l1.

Definition s2 : Z := OCaml.List.length l2.

Definition h {A : Type} (x : A) : M [ OCaml.Failure ] Z :=
  match x with
  | _ => OCaml.List.hd l2
  end.

Definition t {A : Type} (x : A) : M [ OCaml.Failure ] (list Z) :=
  match x with
  | _ => OCaml.List.tl l2
  end.

Definition x {A : Type} (x : A) : M [ OCaml.Failure; OCaml.Invalid_argument ] Z
  :=
  match x with
  | _ => OCaml.List.nth l2 1
  end.

Definition rl : list Z := List.rev l2.

Definition ll : list Z := OCaml.Pervasives.app l2 l2.

Definition rll : list Z := List.rev_append l2 l2.

Definition lc : list Z :=
  OCaml.List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition lf : list Z :=
  OCaml.List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).
