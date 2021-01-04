Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Fixpoint odd_length {A : Set} (l : list A) : bool :=
  match l with
  | [] => false
  | cons _ l => negb (even_length l)
  end

with even_length {A : Set} (l : list A) : bool :=
  match l with
  | [] => true
  | cons _ l => negb (odd_length l)
  end.
