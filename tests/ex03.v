Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition n1 : Z :=
  let m := 12 in
  let n1 := m in
  n1.

Definition n2 : Z :=
  let p1 {A B C : Type} (c : (B -> C -> B) -> A) : A :=
    c (fun x => fun y => x) in
  let c {A : Type} (f : Z -> Z -> A) : A :=
    f 12 23 in
  p1 c.
