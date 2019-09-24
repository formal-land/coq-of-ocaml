Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module SizedString.
  Record t := {
    name : string;
    size : Z }.
End SizedString.

Definition r : SizedString.t :=
  {| SizedString.name := "gre" % string; SizedString.size := 3 |}.

Definition r' : SizedString.t :=
  {| SizedString.name := "haha" % string; SizedString.size := 4 |}.

Definition s : Z := Z.add (SizedString.size r) (SizedString.size r').

Definition f (function_parameter : SizedString.t) : bool :=
  match function_parameter with
  | {| SizedString.size := 3 |} => true
  | _ => false
  end.

Definition b : bool := f r.

Definition b' : bool := f r'.

Module Point.
  Record t := {
    x : Z;
    y : Z;
    z : Z }.
  
  Definition p : t := {| x := 5; y := (-3); z := 1 |}.
  
  Definition b : bool :=
    match p with
    | {| x := 5; z := 1 |} => true
    | _ => false
    end.
End Point.

Record poly {first second : Type} := {
  first : first;
  second : second }.
Arguments poly : clear implicits.
