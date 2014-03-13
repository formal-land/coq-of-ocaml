Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l : M [ Counter; NonTermination ] (list Z) :=
  let fix map_rec {A B : Type} (counter : nat) (f : B -> A) (x : list B) :
    M [ NonTermination ] (list A) :=
    match counter with
    | O => not_terminated tt
    | S counter =>
      match x with
      | [] => ret []
      | cons x xs =>
        let! x_1 := ((map_rec counter) f) xs in
        ret (cons (f x) x_1)
      end
    end in
  let map {A B : Type} (f : B -> A) (x : list B) :
    M [ Counter; NonTermination ] (list A) :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (((map_rec counter) f) x) in
  let fix loop_rec {A : Type} (counter : nat) (x : A) : M [ NonTermination ] A
    :=
    match counter with
    | O => not_terminated tt
    | S counter => ret x
    end in
  let loop {A : Type} (x : A) : M [ Counter; NonTermination ] A :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" ((loop_rec counter) x) in
  (map (fun n => (Z.add n) 1)) (cons 5 (cons 7 (cons 8 []))).
