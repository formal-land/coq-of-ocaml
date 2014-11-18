Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition l {A : Type} (x : A) : M [ Counter; NonTermination ] (list Z) :=
  match x with
  | _ =>
    let fix map_rec {B C : Type} (counter : nat) (f : B -> C) (x_1 : list B)
      : M [ NonTermination ] (list C) :=
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
    let map {B C : Type} (f : B -> C) (x_1 : list B)
      : M [ Counter; NonTermination ] (list C) :=
      let! x_2 := lift [_;_] "10" (read_counter tt) in
      lift [_;_] "01" (map_rec x_2 f x_1) in
    let fix loop_rec {B : Type} (counter : nat) (x : B)
      : M [ NonTermination ] B :=
      match counter with
      | O => not_terminated tt
      | S counter => ret x
      end in
    let loop {B : Type} (x : B) : M [ Counter; NonTermination ] B :=
      let! x_1 := lift [_;_] "10" (read_counter tt) in
      lift [_;_] "01" (loop_rec x_1 x) in
    map (fun n => Z.add n 1) (cons 5 (cons 7 (cons 8 [])))
  end.
