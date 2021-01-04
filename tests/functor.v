Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

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
  forall (P : {t : Set & COMPARABLE.signature (t := t)}),
    {_ : unit & S.signature (t := (|P|).(COMPARABLE.t))}.

Parameter Char : {_ : unit & S.signature (t := ascii)}.

Parameter Abstract : {t : Set & S.signature (t := t)}.
