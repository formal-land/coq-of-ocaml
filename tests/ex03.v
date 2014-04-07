Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition n1 : Z :=
  let m := 12 in
  let n1 := m in
  n1.

Definition n2 : Z :=
  let p1 {A691 A705 A708 : Type} (c : (A705 -> A708 -> A705) -> A691) : A691 :=
    c (fun x => fun y => x) in
  let c {A718 : Type} (f : Z -> Z -> A718) : A718 :=
    f 12 23 in
  p1 c.
