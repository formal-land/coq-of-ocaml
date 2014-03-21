Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition f {A B C : Type} (x : A) : M [ IO ] (C -> M [ Failure ] B) :=
  let! _ := print_string "Hi" % string in
  ret (fun y => failwith "Bye" % string).

Definition r {A B : Type} (x : B) : M [ Failure; IO ] A :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "01" (f 1) in
    lift [_;_] "10" (x_1 2)
  end.
