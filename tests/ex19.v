Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.

Definition Error := Effect.make unit unit.

Definition raise_Error {A : Type} (x : unit) : M [ Error ] A :=
  fun s => (inr (inl x), s).

Definition x1 : Z :=
  match unret (Exception.run 0 (raise_Error tt) tt) with
  | inl x => x
  | inr tt => 12
  end.

Definition x2 {A B : Type} (x : A) : M [ OCaml.Failure ] B :=
  match x with
  | _ =>
    match unret (Exception.run 0 (raise_Error tt) tt) with
    | inl x => ret x
    | inr tt => OCaml.Pervasives.failwith "arg" % string
    end
  end.

Definition x3 (b : bool) : M [ OCaml.Failure ] Z :=
  let! x :=
    Exception.run 1
      (if b then
        lift [_;_] "10" (OCaml.Pervasives.failwith "arg" % string)
      else
        lift [_;_] "01" (raise_Error tt)) tt in
  match x with
  | inl x => ret x
  | inr tt => ret 12
  end.
