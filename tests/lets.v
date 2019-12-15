Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition n1 : Z :=
  let m := 12 in
  let n1 := m in
  n1.

Definition n2 : Z :=
  let p1 {A B C : Type} (c : (A -> B -> A) -> C) : C :=
    c (fun x => fun y => x) in
  let c {A : Type} (f : Z -> Z -> A) : A :=
    f 12 23 in
  p1 c.
