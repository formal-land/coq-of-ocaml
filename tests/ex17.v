Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition TailLess := Effect.new unit unit.

Definition raise_TailLess {A : Type} (x : unit) : M [ TailLess ] A :=
  fun s => (inr (inl x), s).

Definition Wtf := Effect.new unit (Z * string).

Definition raise_Wtf {A : Type} (x : Z * string) : M [ Wtf ] A :=
  fun s => (inr (inl x), s).

Definition f {A B : Type} (x : B) : M [ TailLess ] A := raise_TailLess tt.

Definition g {A B : Type} (x : B) : M [ Wtf ] A :=
  raise_Wtf (12, "no" % string).

Fixpoint h_rec {A : Type} (counter : nat) (l : list A) :
  M [ IO; NonTermination; TailLess ] A :=
  match counter with
  | 0 % nat => lift [_;_;_] "010" (not_terminated tt)
  | S counter =>
    match l with
    | [] =>
      lift [_;_;_] "101"
        (let! _ := lift [_;_] "10" (print_string "no tail" % string) in
        lift [_;_] "01" (raise_TailLess tt))
    | cons x [] => ret x
    | cons _ xs => (h_rec counter) xs
    end
  end.

Definition h {A : Type} (l : list A) :
  M [ Counter; IO; NonTermination; TailLess ] A :=
  let! counter := lift [_;_;_;_] "1000" (read_counter tt) in
  lift [_;_;_;_] "0111" ((h_rec counter) l).
