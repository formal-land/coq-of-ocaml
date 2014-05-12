Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition tail {A : Type} (l : list A) : M [ OCaml.Failure ] (list A) :=
  match l with
  | cons _ xs => ret xs
  | [] =>
    OCaml.Pervasives.failwith "Cannot take the tail of an empty list." % string
  end.

Fixpoint print_list_rec (counter : nat) (x : list string)
  : M [ IO; NonTermination ] unit :=
  match counter with
  | O => lift [_;_] "01" (not_terminated tt)
  | S counter =>
    match x with
    | [] => ret tt
    | cons x xs =>
      let! _ := lift [_;_] "10" (OCaml.Pervasives.print_string x) in
      (print_list_rec counter) xs
    end
  end.

Definition print_list (x : list string)
  : M [ Counter; IO; NonTermination ] unit :=
  let! x_1 := lift [_;_;_] "100" (read_counter tt) in
  lift [_;_;_] "011" (print_list_rec x_1 x).

Definition f : (list string) -> M [ Counter; IO; NonTermination ] unit :=
  print_list.

Definition x {A : Type} (z : A)
  : M [ Counter; IO; NonTermination; OCaml.Failure ] unit :=
  let! x :=
    lift [_;_;_;_] "0001"
      (tail
        (cons "Stop" % string
          (cons "Hello" % string (cons " " % string (cons "world" % string [])))))
    in
  lift [_;_;_;_] "1110" (f x).
