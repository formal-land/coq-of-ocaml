Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition Outside := Effect.make unit unit.

Definition raise_Outside {A : Type} (x : unit) : M [ Outside ] A :=
  fun s => (inr (inl x), s).

Definition f {A B : Type} (x : B) : M [ Outside ] A := raise_Outside tt.

Module G.
  Definition Inside := Effect.make unit (Z * string).
  
  Definition raise_Inside {A : Type} (x : Z * string) : M [ Inside ] A :=
    fun s => (inr (inl x), s).
  
  Definition g {A : Type} (b : bool) : M [ Outside; Inside ] A :=
    if b then
      lift [_;_] "01" (raise_Inside (12, "no" % string))
    else
      lift [_;_] "10" (raise_Outside tt).
End G.

Fixpoint h_rec {A B : Type} (counter : nat) (l : list B) :
  M [ Outside; G.Inside; IO; NonTermination ] A :=
  match counter with
  | O => lift [_;_;_;_] "0001" (not_terminated tt)
  | S counter =>
    match l with
    | [] =>
      lift [_;_;_;_] "1110"
        (let! _ := lift [_;_;_] "001" (print_string "no tail" % string) in
        lift [_;_;_] "110" (G.g false))
    | cons x [] => lift [_;_;_;_] "0100" (G.raise_Inside (0, "gg" % string))
    | cons _ xs => (h_rec counter) xs
    end
  end.

Definition h {A B : Type} (l : list B) :
  M [ Outside; G.Inside; Counter; IO; NonTermination ] A :=
  let! x :=
    lift [_;_;_;_;_] "00100"
      (let! x := read_counter tt in
      ret (h_rec x)) in
  lift [_;_;_;_;_] "11011" (x l).
