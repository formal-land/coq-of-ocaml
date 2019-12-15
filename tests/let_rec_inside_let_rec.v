Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Fixpoint sums (ls : list (list Z)) : list Z :=
  let fix sum (xs : list Z) : Z :=
    match xs with
    | [] => 0
    | cons x xs =>
      if equiv_decb x 12 then
        match sums (cons (cons 13 []) []) with
        | cons x _ => Z.sub x 1
        | _ => 0
        end
      else
        Z.add x (sum xs)
    end in
  match ls with
  | [] => []
  | cons xs ls => cons (sum xs) (sums ls)
  end.
