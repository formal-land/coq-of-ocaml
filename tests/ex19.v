Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition Error := Effect.make unit unit.

Definition raise_Error {A : Type} (x : unit) : M [ Error ] A :=
  fun s => (inr (inl x), s).

Definition x1 : Z :=
  match unret (Exception.run 0 (raise_Error tt) tt) with
  | inl x => x
  | inr tt => 12
  end.

Definition x2 {A B : Type} (x : B) : M [ Failure ] A :=
  match x with
  | _ =>
    match unret (Exception.run 0 (raise_Error tt) tt) with
    | inl x => ret x
    | inr tt => failwith "arg" % string
    end
  end.

Definition x3 (b : bool) : M [ Failure ] Z :=
  let! x :=
    Exception.run 0
      (if b then
        lift [_;_] "01" (failwith "arg" % string)
      else
        lift [_;_] "10" (raise_Error tt)) tt in
  match x with
  | inl x => ret x
  | inr tt => ret 12
  end.
