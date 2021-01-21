Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module T_bytes.
  Record signature {t : Set} : Set := {
    t := t;
    to_bytes : t -> bytes;
    of_bytes_exn : bytes -> t;
  }.
End T_bytes.

Module T_encoding.
  Record signature {t : Set} : Set := {
    t := t;
    encoding : list t;
  }.
End T_encoding.

Module T_encoding_bytes.
  Record signature {t : Set} : Set := {
    t := t;
    to_bytes : t -> bytes;
    of_bytes_exn : bytes -> t;
    encoding : list t;
  }.
End T_encoding_bytes.

Module WithBar.
  Record signature : Set := {
    bar : string;
  }.
End WithBar.

Module Validator.
  Record signature
    {Ciphertext_t Commitment_t Commitment_NestedLevel_t CV_t : Set} : Set := {
    Ciphertext_t := Ciphertext_t;
    Ciphertext_encoding : list Ciphertext_t;
    Ciphertext_get_memo_size : Ciphertext_t -> int;
    Commitment_v : string;
    Commitment_t := Commitment_t;
    Commitment_to_bytes : Commitment_t -> bytes;
    Commitment_of_bytes_exn : bytes -> Commitment_t;
    Commitment_encoding : list Commitment_t;
    Commitment_valid_position : int64 -> bool;
    Commitment_Foo : WithBar.signature;
    Commitment_NestedLevel_t := Commitment_NestedLevel_t;
    CV : T_encoding.signature (t := CV_t);
    com := Commitment_t;
  }.
End Validator.

Module F.
  Class FArgs
    {V_Ciphertext_t V_Commitment_t V_Commitment_NestedLevel_t V_CV_t : Set} := {
    V :
      Validator.signature (Ciphertext_t := V_Ciphertext_t)
        (Commitment_t := V_Commitment_t)
        (Commitment_NestedLevel_t := V_Commitment_NestedLevel_t)
        (CV_t := V_CV_t);
  }.
  Arguments Build_FArgs {_ _ _ _}.
  
  Definition foo `{FArgs} : Set :=
    V.(Validator.Commitment_t) * V.(Validator.Commitment_NestedLevel_t).
  
  Definition bar `{FArgs} : string :=
    V.(Validator.Commitment_Foo).(WithBar.bar).
  
  Definition functor `{FArgs} :=
    {|
      WithBar.bar := bar
    |}.
End F.
Definition F
  {V_Ciphertext_t V_Commitment_t V_Commitment_NestedLevel_t V_CV_t : Set}
  (V :
    Validator.signature (Ciphertext_t := V_Ciphertext_t)
      (Commitment_t := V_Commitment_t)
      (Commitment_NestedLevel_t := V_Commitment_NestedLevel_t) (CV_t := V_CV_t))
  : WithBar.signature :=
  let '_ := F.Build_FArgs V in
  F.functor.
