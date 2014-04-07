Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition f {A687 A698 A701 : Type} (x : A687) :
  M [ IO ] (A701 -> M [ OCaml.Failure ] A698) :=
  let! _ := OCaml.Pervasives.print_string "Hi" % string in
  ret (fun y => OCaml.Pervasives.failwith "Bye" % string).

Definition r {A715 A718 : Type} (x : A718) : M [ IO; OCaml.Failure ] A715 :=
  match x with
  | _ =>
    let! x_1 := lift [_;_] "10" (f 1) in
    lift [_;_] "01" (x_1 2)
  end.
