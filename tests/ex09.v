Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l : M [ Ref_Counter; Err_NonTermination ] (list Z) :=
  let fix map_rec {A B : Type}
    (counter : nat) (f : B -> A) (match_var_0 : list B) :
    M [ Err_NonTermination ] (list A) :=
    match counter with
    | 0 % nat => not_terminated tt
    | S counter =>
      match match_var_0 with
      | [] => ret []
      | cons x xs =>
        let! x_1 := ((map_rec counter) f) xs in
        ret (cons (f x) x_1)
      end
    end in
  let map {A B : Type} (f : B -> A) (match_var_0 : list B) :
    M [ Ref_Counter; Err_NonTermination ] (list A) :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (((map_rec counter) f) match_var_0) in
  let fix loop_rec {A : Type} (counter : nat) (x : A) :
    M [ Err_NonTermination ] A :=
    match counter with
    | 0 % nat => not_terminated tt
    | S counter => ret x
    end in
  let loop {A : Type} (x : A) : M [ Ref_Counter; Err_NonTermination ] A :=
    let! counter := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" ((loop_rec counter) x) in
  (map (fun n => (Z.add n) 1)) (cons 5 (cons 7 (cons 8 []))).
