Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive t1 : Type :=
| C1 : Z -> t1
| C2 : bool -> Z -> t1
| C3 : t1 .
Arguments C1 _.
Arguments C2 _ _.
Arguments C3 .

Definition n : t1 := C2 false 3.

Definition m : bool :=
  match n with
  | C2 b _ => b
  | _ => true
  end.

Inductive t2 (a : Type) : Type :=
| D1 : t2 a
| D2 : a -> (t2 a) -> t2 a.
Arguments D1 {a} .
Arguments D2 {a} _ _.

Fixpoint of_list {A : Type} (l : list A) : t2 A :=
  match l with
  | [] => D1
  | cons x xs => D2 x (of_list xs)
  end.

Fixpoint sum (l : t2 Z) : Z :=
  match l with
  | D1 => 0
  | D2 x xs => (Z.add x) (sum xs)
  end.

Definition s : Z := sum (of_list (cons 5 (cons 7 (cons 3 [])))).
