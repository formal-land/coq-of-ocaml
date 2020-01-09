Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module SizedString.
  Module t.
    Record record := {
      name : string;
      size : Z }.
  End t.
  Definition t := t.record.
End SizedString.

Definition r : SizedString.t :=
  {| SizedString.t.name := "gre" % string; SizedString.t.size := 3 |}.

Definition r' : SizedString.t :=
  {| SizedString.t.name := "haha" % string; SizedString.t.size := 4 |}.

Definition s : Z := Z.add (SizedString.t.size r) (SizedString.t.size r').

Definition f (function_parameter : SizedString.t) : bool :=
  match function_parameter with
  | {| SizedString.t.size := 3 |} => true
  | _ => false
  end.

Definition b : bool := f r.

Definition b' : bool := f r'.

Module Point.
  Module t.
    Record record := {
      x : Z;
      y : Z;
      z : Z }.
  End t.
  Definition t := t.record.
  
  Definition p : t := {| t.x := 5; t.y := (-3); t.z := 1 |}.
  
  Definition b : bool :=
    match p with
    | {| t.x := 5; t.z := 1 |} => true
    | _ => false
    end.
End Point.

Module poly.
  Record record {first second : Set} := {
    first : first;
    second : second }.
  Arguments record : clear implicits.
End poly.
Definition poly := poly.record.

Definition p : poly Z bool := {| poly.first := 12; poly.second := false |}.
