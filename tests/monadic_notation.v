Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition __return {a : Set} (x : a) : option a := Some x.

Definition op_letstar {a b : Set} (x : option a) (f : a -> option b)
  : option b :=
  match x with
  | Some x => f x
  | None => None
  end.

Definition get_head {A : Set} (l : list A) : option A :=
  match l with
  | [] => None
  | cons x _ => Some x
  end.

Notation "'let*' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x ident, X at level 100, Y at level 200).

Notation "'let*' ' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).

Definition sum_first_elements (l1 : list int) (l2 : list (int * int))
  : option int :=
  let* x1 := get_head l1 in
  let* '(x2, x3) := get_head l2 in
  __return (Z.add (Z.add x1 x2) x3).
