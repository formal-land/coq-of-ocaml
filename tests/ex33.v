Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module Type M.
  Parameter n : Z.
  
  Parameter f : forall {a b : Type}, a -> a * b.
  
  Inductive t1 (a : Type) : Type :=
  | C1 : Z -> t1 a
  | C2 : a -> bool -> t1 a.
  Arguments C1 {a} _.
  Arguments C2 {a} _ _.
  
  Record t2 := {
    f1 : Z;
    f2 : bool }.
  
  Definition t3 a := Z * a.
  
  Parameter t4 : Type.
  
  Parameter t5 : forall {a b : Type}, Type.
  
  Definition E := Effect.make unit (string).
  
  Definition raise_E {A : Type} (x : string) : M [ E ] A :=
    fun s => (inr (inl x), s).
End M.
