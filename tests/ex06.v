Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint map_rec {A704 A709 : Type}
  (counter : nat) (f : A709 -> A704) (l : list A709) :
  M [ NonTermination ] (list A704) :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret []
    | cons x xs =>
      let! x_1 := (map_rec counter) f xs in
      ret (cons (f x) x_1)
    end
  end.

Definition map {A704 A709 : Type} (f : A709 -> A704) (l : list A709) :
  M [ Counter; NonTermination ] (list A704) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (map_rec x f l).

Fixpoint fold_rec {A753 A756 : Type}
  (counter : nat) (f : A753 -> A756 -> A753) (a : A753) (l : list A756) :
  M [ NonTermination ] A753 :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret a
    | cons x xs => (fold_rec counter) f (f a x) xs
    end
  end.

Definition fold {A753 A756 : Type}
  (f : A753 -> A756 -> A753) (a : A753) (l : list A756) :
  M [ Counter; NonTermination ] A753 :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (fold_rec x f a l).

Definition l : list Z := cons 5 (cons 6 (cons 7 (cons 2 []))).

Definition n {A818 : Type} (incr : Z -> A818) (plus : Z -> A818 -> Z) :
  M [ Counter; NonTermination ] Z :=
  let! x := map incr l in
  fold (fun x => fun y => plus x y) 0 x.
