Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module COMPARABLE.
  Record signature {t : Set} : Set := {
    t := t;
    compare : t -> t -> int;
  }.
End COMPARABLE.

Module S.
  Record signature {t : Set} : Set := {
    t := t;
    op_eq : t -> t -> bool;
    op_ltgt : t -> t -> bool;
    op_lt : t -> t -> bool;
    op_lteq : t -> t -> bool;
    op_gteq : t -> t -> bool;
    op_gt : t -> t -> bool;
    compare : t -> t -> int;
    equal : t -> t -> bool;
    max : t -> t -> t;
    min : t -> t -> t;
  }.
End S.

Parameter Make :
  forall {P_t : Set},
  forall (P : COMPARABLE.signature (t := P_t)),
  S.signature (t := P.(COMPARABLE.t)).

Parameter Char : S.signature (t := ascii).

Parameter Abstract_t : Set.

Parameter Abstract : S.signature (t := Abstract_t).

Parameter Lift_t :
  forall {P_t : Set} (P : COMPARABLE.signature (t := P_t)), Set.

Parameter Lift :
  forall {P_t : Set},
  forall (P : COMPARABLE.signature (t := P_t)),
  COMPARABLE.signature (t := Lift_t P).
