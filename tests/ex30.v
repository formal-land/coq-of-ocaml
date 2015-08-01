Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module M.
  Definition f {A B : Type} (x : A) : M [ OCaml.Failure ] B :=
    match x with
    | _ => OCaml.Pervasives.failwith "failure" % string
    end.
End M.

Module N.
  Definition f {A B : Type} (x : A) : M [ OCaml.Assert_failure ] B :=
    match x with
    | _ => OCaml.assert false
    end.
  
  Definition x : unit :=
    match Exception.run 0 (f tt) tt with
    | inl x => x
    | inr (_) => tt
    end.
  
  Import M.
  
  Definition y : unit :=
    match Exception.run 0 (M.f tt) tt with
    | inl x => x
    | inr (_) => tt
    end.
End N.

Definition b : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (_) => tt
  end.

Import N.

Definition b' : unit :=
  match Exception.run 0 (N.f tt) tt with
  | inl x => x
  | inr (_) => tt
  end.
