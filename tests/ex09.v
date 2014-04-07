Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l {A687 : Type} (x : A687) : M [ Counter; NonTermination ] (list Z)
  :=
  match x with
  | _ =>
    let fix map_rec {A707 A712 : Type}
      (counter : nat) (f : A712 -> A707) (x_1 : list A712) :
      M [ NonTermination ] (list A707) :=
      match counter with
      | O => not_terminated tt
      | S counter =>
        match x_1 with
        | [] => ret []
        | cons x xs =>
          let! x_2 := (map_rec counter) f xs in
          ret (cons (f x) x_2)
        end
      end in
    let map {A707 A712 : Type} (f : A712 -> A707) (x_1 : list A712) :
      M [ Counter; NonTermination ] (list A707) :=
      let! x_2 := lift [_;_] "10" (read_counter tt) in
      lift [_;_] "01" (map_rec x_2 f x_1) in
    let fix loop_rec {A727 : Type} (counter : nat) (x : A727) :
      M [ NonTermination ] A727 :=
      match counter with
      | O => not_terminated tt
      | S counter => ret x
      end in
    let loop {A727 : Type} (x : A727) : M [ Counter; NonTermination ] A727 :=
      let! x_1 := lift [_;_] "10" (read_counter tt) in
      lift [_;_] "01" (loop_rec x_1 x) in
    map (fun n => Z.add n 1) (cons 5 (cons 7 (cons 8 [])))
  end.
