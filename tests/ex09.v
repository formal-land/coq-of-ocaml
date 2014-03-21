Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l {A : Type} (x : A) : M [ Counter; NonTermination ] (list Z) :=
  match x with
  | _ =>
    let fix map_rec {A B : Type} (counter : nat) (f : B -> A) (x_1 : list B) :
      M [ NonTermination ] (list A) :=
      match counter with
      | O => not_terminated tt
      | S counter =>
        match x_1 with
        | [] => ret []
        | cons x xs =>
          let! x_2 := ((map_rec counter) f) xs in
          ret (cons (f x) x_2)
        end
      end in
    let map {A B : Type} (f : B -> A) (x_1 : list B) :
      M [ Counter; NonTermination ] (list A) :=
      let! x_2 :=
        lift [_;_] "10"
          (let! x_2 :=
            let! x_2 := read_counter tt in
            ret (map_rec x_2) in
          ret (x_2 f)) in
      lift [_;_] "01" (x_2 x_1) in
    let fix loop_rec {A : Type} (counter : nat) (x : A) : M [ NonTermination ] A
      :=
      match counter with
      | O => not_terminated tt
      | S counter => ret x
      end in
    let loop {A : Type} (x : A) : M [ Counter; NonTermination ] A :=
      let! x_1 :=
        lift [_;_] "10"
          (let! x_1 := read_counter tt in
          ret (loop_rec x_1)) in
      lift [_;_] "01" (x_1 x) in
    (map (fun n => (Z.add n) 1)) (cons 5 (cons 7 (cons 8 [])))
  end.
