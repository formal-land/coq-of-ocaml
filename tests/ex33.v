Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module Type IM1.
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
End IM1.

Module Type IM2.
  Parameter t : Type.
  
  Parameter m : Z.
  
  Parameter b : t.
End IM2.

Module M2.
  Definition null : Z * bool := (0, false).
  
  Definition t := bool.
  
  Definition m : Z := 12.
  
  Definition b : bool := false.
End M2.
