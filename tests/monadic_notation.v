Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition _return {a : Set} (x_value : a) : option a := Some x_value.

Definition op_letstar {a b : Set} (x_value : option a) (f_value : a -> option b)
  : option b :=
  match x_value with
  | Some x_value => f_value x_value
  | None => None
  end.

Definition get_head {A : Set} (l_value : list A) : option A :=
  match l_value with
  | [] => None
  | cons x_value _ => Some x_value
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
  _return (Z.add (Z.add x1 x2) x3).
