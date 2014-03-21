Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint sums_rec (counter : nat) (ls : list (list Z)) :
  M [ Counter; NonTermination ] (list Z) :=
  match counter with
  | O => lift [_;_] "01" (not_terminated tt)
  | S counter =>
    let fix sum_rec (counter_1 : nat) (xs : list Z) :
      M [ Counter; NonTermination ] Z :=
      match counter_1 with
      | O => lift [_;_] "01" (not_terminated tt)
      | S counter_1 =>
        match xs with
        | [] => ret 0
        | cons x xs =>
          if (equiv_decb x) 12 then
            let! x_1 := (sums_rec counter) (cons (cons 13 []) []) in
            match x_1 with
            | cons x _ => ret ((Z.sub x) 1)
            | _ => ret 0
            end
          else
            let! x_1 := (sum_rec counter_1) xs in
            ret ((Z.add x) x_1)
        end
      end in
    let sum (xs : list Z) : M [ Counter; NonTermination ] Z :=
      let! x :=
        lift [_;_] "10"
          (let! x := read_counter tt in
          ret (sum_rec x)) in
      x xs in
    match ls with
    | [] => ret []
    | cons xs ls =>
      let! x := sum xs in
      let! x_1 := (sums_rec counter) ls in
      ret (cons x x_1)
    end
  end.

Definition sums (ls : list (list Z)) : M [ Counter; NonTermination ] (list Z) :=
  let! x :=
    lift [_;_] "10"
      (let! x := read_counter tt in
      ret (sums_rec x)) in
  x ls.
