Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module COMPARABLE.
  Record signature {t : Set} : Set := {
    t := t;
    compare : t -> t -> int;
  }.
End COMPARABLE.
Definition COMPARABLE := @COMPARABLE.signature.
Arguments COMPARABLE {_}.

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
Definition S := @S.signature.
Arguments S {_}.

Parameter Make :
  forall {P_t : Set},
  forall (P : COMPARABLE (t := P_t)), S (t := P.(COMPARABLE.t)).

Parameter Char : S (t := ascii).

Parameter Abstract_t : Set.

Parameter Abstract : S (t := Abstract_t).

Parameter Lift_t : forall {P_t : Set} (P : COMPARABLE (t := P_t)), Set.

Parameter Lift :
  forall {P_t : Set},
  forall (P : COMPARABLE (t := P_t)), COMPARABLE (t := Lift_t P).
