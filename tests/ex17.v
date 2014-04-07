Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition Outside := Effect.make unit unit.

Definition raise_Outside {A : Type} (x : unit) : M [ Outside ] A :=
  fun s => (inr (inl x), s).

Definition f {A684 A687 : Type} (x : A687) : M [ Outside ] A684 :=
  raise_Outside tt.

Module G.
  Definition Inside := Effect.make unit (Z * string).
  
  Definition raise_Inside {A : Type} (x : Z * string) : M [ Inside ] A :=
    fun s => (inr (inl x), s).
  
  Definition g {A705 : Type} (b : bool) : M [ Outside; Inside ] A705 :=
    if b then
      lift [_;_] "01" (raise_Inside (12, "no" % string))
    else
      lift [_;_] "10" (raise_Outside tt).
End G.

Fixpoint h_rec {A731 A753 : Type} (counter : nat) (l : list A753) :
  M [ IO; NonTermination; Outside; G.Inside ] A731 :=
  match counter with
  | O => lift [_;_;_;_] "0100" (not_terminated tt)
  | S counter =>
    match l with
    | [] =>
      lift [_;_;_;_] "1011"
        (let! _ :=
          lift [_;_;_] "100" (OCaml.Pervasives.print_string "no tail" % string)
          in
        lift [_;_;_] "011" (G.g false))
    | cons x [] => lift [_;_;_;_] "0001" (G.raise_Inside (0, "gg" % string))
    | cons _ xs => (h_rec counter) xs
    end
  end.

Definition h {A731 A753 : Type} (l : list A753) :
  M [ Counter; IO; NonTermination; Outside; G.Inside ] A731 :=
  let! x := lift [_;_;_;_;_] "10000" (read_counter tt) in
  lift [_;_;_;_;_] "01111" (h_rec x l).
