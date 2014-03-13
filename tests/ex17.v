Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition Outside := Effect.new unit unit.

Definition raise_Outside {A : Type} (x : unit) : M [ Outside ] A :=
  fun s => (inr (inl x), s).

Definition f {A B : Type} (x : B) : M [ Outside ] A := raise_Outside tt.

Module G.
  Definition Inside := Effect.new unit (Z * string).
  
  Definition raise_Inside {A : Type} (x : Z * string) : M [ Inside ] A :=
    fun s => (inr (inl x), s).
  
  Definition g {A : Type} (b : bool) : M [ Inside; Outside ] A :=
    if b then
      lift [_;_] "10" (raise_Inside (12, "no" % string))
    else
      lift [_;_] "01" (raise_Outside tt).
End G.

Fixpoint h_rec {A B : Type} (counter : nat) (l : list B) :
  M [ IO; G.Inside; NonTermination; Outside ] A :=
  match counter with
  | O => lift [_;_;_;_] "0010" (not_terminated tt)
  | S counter =>
    match l with
    | [] =>
      lift [_;_;_;_] "1101"
        (let! _ := lift [_;_;_] "100" (print_string "no tail" % string) in
        lift [_;_;_] "011" (G.g false))
    | cons x [] => lift [_;_;_;_] "0100" (G.raise_Inside (0, "gg" % string))
    | cons _ xs => (h_rec counter) xs
    end
  end.

Definition h {A B : Type} (l : list B) :
  M [ Counter; IO; G.Inside; NonTermination; Outside ] A :=
  let! counter := lift [_;_;_;_;_] "10000" (read_counter tt) in
  lift [_;_;_;_;_] "01111" ((h_rec counter) l).
