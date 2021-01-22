Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module Sig1.
  Record signature {t : Set} : Set := {
    t := t;
    f : t -> t -> t * t;
  }.
End Sig1.
Definition Sig1 := @Sig1.signature.
Arguments Sig1 {_}.

Module Sig2.
  Record signature {t : Set} : Set := {
    t := t;
    f : t -> list t;
  }.
End Sig2.
Definition Sig2 := @Sig2.signature.
Arguments Sig2 {_}.

Module M1.
  Definition t : Set := int.
  
  Definition f {A : Set} (n : t) (m : A) : t * A := (n, m).
  
  Definition module :=
    {|
      Sig1.f := f
    |}.
End M1.
Definition M1 : Sig1 (t := _) := M1.module.

Module M2.
  Definition t : Set := int.
  
  Definition f {A : Set} (n : t) : list A := nil.
  
  Definition module :=
    {|
      Sig2.f := f
    |}.
End M2.
Definition M2 : Sig2 (t := _) := M2.module.
