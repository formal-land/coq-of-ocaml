Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition n1 : int :=
  let m := 12 in
  let n1 := m in
  n1.

Definition n2 : int :=
  let p1 {A B C : Set} (c : (A -> B -> A) -> C) : C :=
    c (fun (x : A) => fun (y : B) => x) in
  let c {A : Set} (f : int -> int -> A) : A :=
    f 12 23 in
  p1 c.
