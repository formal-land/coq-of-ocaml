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
Definition F_definition {M1_t M2_t : Set}
  (M1 : S.signature (t := M1_t)) (M2 : S.signature (t := M2_t))
  : S.signature (t := M1.(S.t) * M2.(S.t) * string) :=
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
Definition F_abstract {M1_t M2_t : Set}
  (M1 : S.signature (t := M1_t)) (M2 : S.signature (t := M2_t))
  : S.signature (t := _) :=
  let '_ := F_abstract.Build_FArgs M1 M2 in
  F_abstract.functor.

Module S_with_functor.
  Record signature : Set := {
    F :
      forall {M_t : Set},
      forall (M : S.signature (t := M_t)), S.signature (t := M.(S.t) * int);
  }.
End S_with_functor.

Module M_with_functor.
  Module F.
    Class FArgs {M_t : Set} := {
      M : S.signature (t := M_t);
    }.
    Arguments Build_FArgs {_}.
    
    Definition t `{FArgs} : Set := M.(S.t) * int.
    
    Definition v `{FArgs} : M.(S.t) * int := (M.(S.v), 12).
    
    Definition functor `{FArgs} :=
      {|
        S.v := v
      |}.
  End F.
  Definition F {M_t : Set} (M : S.signature (t := M_t)) :=
    let '_ := F.Build_FArgs M in
    F.functor.
  
  Definition module :=
    {|
      S_with_functor.F _ := F
    |}.
End M_with_functor.
Definition M_with_functor : S_with_functor.signature := M_with_functor.module.
