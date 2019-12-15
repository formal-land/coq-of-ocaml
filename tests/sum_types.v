Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive t1 : Type :=
| C1 : Z -> t1
| C2 : bool -> Z -> t1
| C3 : t1.

Definition n : t1 := C2 false 3.

Definition m : bool :=
  match n with
  | C2 b _ => b
  | _ => true
  end.

Inductive t2 (a : Type) : Type :=
| D1 : t2 a
| D2 : a -> (t2 a) -> t2 a.

Arguments D1 {_}.
Arguments D2 {_}.

Fixpoint of_list {A : Type} (l : list A) : t2 A :=
  match l with
  | [] => D1
  | cons x xs => D2 x (of_list xs)
  end.

Fixpoint sum (l : t2 Z) : Z :=
  match l with
  | D1 => 0
  | D2 x xs => Z.add x (sum xs)
  end.

Definition s {A : Type} (function_parameter : A) : Z :=
  let '_ := function_parameter in
  sum (of_list (cons 5 (cons 7 (cons 3 [])))).

Parameter t3 : Type.

Parameter t4 : forall (a : Type), Type.

Inductive t5 : Type :=
| C : t5.

Inductive single_string : Type :=
| Single : string -> single_string.

Definition get_string (s : single_string) : string :=
  let 'Single s := s in
  s.
