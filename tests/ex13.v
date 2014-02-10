Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition tail {A : Type} (l : list A) : M [ Failure ] (list A) :=
  match l with
  | cons _ xs => ret xs
  | [] => failwith "Cannot take the tail of an empty list." % string
  end.

Fixpoint print_list (match_var_0 : list string) : M [ IO ] unit :=
  match match_var_0 with
  | [] => ret tt
  | cons x xs =>
    let! _ := print_string x in
    print_list xs
  end.

Definition f : (list string) -> M [ IO ] unit := print_list.

Definition x {A : Type} (z : A) : M [ Failure; IO ] unit :=
  let! x :=
    lift [_;_] "10"
      (tail
        (cons "Stop" % string
          (cons "Hello" % string (cons " " % string (cons "world" % string [])))))
    in
  lift [_;_] "01" (f x).
