Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module S.
  Record signature {t : Set} : Set := {
    t := t;
    v : t;
  }.
End S.

Module M_infer.
  Definition t : Set := int.
  
  Definition v : int := 12.
  
  Definition module :=
    {|
      S.v := v
    |}.
End M_infer.
Definition M_infer := M_infer.module.

Module M_definition.
  Definition t : Set := int.
  
  Definition v : int := 12.
  
  Definition module :=
    {|
      S.v := v
    |}.
End M_definition.
Definition M_definition : S.signature (t := int) := M_definition.module.

Module M_abstract.
  Definition t : Set := int.
  
  Definition v : int := 12.
  
  Definition module :=
    {|
      S.v := v
    |}.
End M_abstract.
Definition M_abstract : S.signature (t := _) := M_abstract.module.

Module F_definition.
  Class FArgs {M1_t M2_t : Set} := {
    M1 : S.signature (t := M1_t);
    M2 : S.signature (t := M2_t);
  }.
  Arguments Build_FArgs {_ _}.
  
  Definition t `{FArgs} : Set := M1.(S.t) * M2.(S.t) * string.
  
  Definition v `{FArgs} : M1.(S.t) * M2.(S.t) * string :=
    (M1.(S.v), M2.(S.v), "foo").
  
  Definition functor `{FArgs} :=
    {|
      S.v := v
    |}.
End F_definition.
Definition F_definition {M1_t : Set} (M1 : S.signature (t := M1_t))
  {M2_t : Set} (M2 : S.signature (t := M2_t)) :
  S.signature (t := M1.(S.t) * M2.(S.t) * string) :=
  let '_ := F_definition.Build_FArgs M1 M2 in
  F_definition.functor.

Module F_abstract.
  Class FArgs {M1_t M2_t : Set} := {
    M1 : S.signature (t := M1_t);
    M2 : S.signature (t := M2_t);
  }.
  Arguments Build_FArgs {_ _}.
  
  Definition t `{FArgs} : Set := M1.(S.t) * M2.(S.t) * string.
  
  Definition v `{FArgs} : M1.(S.t) * M2.(S.t) * string :=
    (M1.(S.v), M2.(S.v), "foo").
  
  Definition functor `{FArgs} :=
    {|
      S.v := v
    |}.
End F_abstract.
Definition F_abstract {M1_t : Set} (M1 : S.signature (t := M1_t))
  {M2_t : Set} (M2 : S.signature (t := M2_t)) : S.signature (t := _) :=
  let '_ := F_abstract.Build_FArgs M1 M2 in
  F_abstract.functor.
