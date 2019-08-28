Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module S.
  Record SET {elt t : Type} := {
    elt := elt;
    t := t;
    empty : t;
    is_empty : t -> bool;
    mem : elt -> t -> bool;
    add : elt -> t -> t;
    singleton : elt -> t;
    remove : elt -> t -> t;
    union : t -> t -> t;
    inter : t -> t -> t;
    diff : t -> t -> t;
    compare : t -> t -> Z;
    equal : t -> t -> bool;
    subset : t -> t -> bool;
    iter : (elt -> unit) -> t -> unit;
    map : (elt -> elt) -> t -> t;
    fold : forall {a : Type}, (elt -> a -> a) -> t -> a -> a;
    for_all : (elt -> bool) -> t -> bool;
    _exists : (elt -> bool) -> t -> bool;
    filter : (elt -> bool) -> t -> t;
    partition : (elt -> bool) -> t -> t * t;
    cardinal : t -> Z;
    elements : t -> list elt;
    min_elt_opt : t -> option elt;
    max_elt_opt : t -> option elt;
    choose_opt : t -> option elt;
    split : elt -> t -> t * bool * t;
    find_opt : elt -> t -> option elt;
    find_first_opt : (elt -> bool) -> t -> option elt;
    find_last_opt : (elt -> bool) -> t -> option elt;
    of_list : (list elt) -> t;
  }.
  Arguments SET : clear implicits.
End S.

Inductive type_annot : Type :=
| Type_annot : string -> type_annot.

Inductive field_annot : Type :=
| Field_annot : string -> field_annot.

Definition pair (a b : Type) := a * b.

Inductive comb : Type :=
| Comb : comb.

Inductive leaf : Type :=
| Leaf : leaf.

Inductive comparable_struct : forall (_ _ : Type), Type :=
| Int_key : forall (position : Type), (option type_annot) ->
  comparable_struct Z position
| String_key : forall (position : Type), (option type_annot) ->
  comparable_struct string position
| Bool_key : forall (position : Type), (option type_annot) ->
  comparable_struct bool position
| Pair_key : forall (a b position : Type),
  ((comparable_struct a leaf) * (option field_annot)) ->
  ((comparable_struct b position) * (option field_annot)) -> (option type_annot)
  -> comparable_struct (pair a b) comb.
Arguments Int_key {position} _.
Arguments String_key {position} _.
Arguments Bool_key {position} _.
Arguments Pair_key {a b position} _ _ _.

Definition comparable_ty (a : Type) := comparable_struct a comb.

Record Boxed_set {elt : Type} := {
  elt := elt;
  elt_ty : comparable_ty elt;
  OPS : {t : Type & S.SET elt t};
  OPS' : {'(elt, t) : _ & S.SET elt t};
  OPS'' : {_ : unit & S.SET elt (list string)};
  boxed : (projT2 OPS).(S.t);
  size : Z;
  table (a : Type) := list a;
}.
Arguments Boxed_set : clear implicits.

Record Triple {a b c : Type} := {
  a := a;
  b := b;
  c := c;
}.
Arguments Triple : clear implicits.

Record UsingTriple := {
  T : {'(a, b, c) : _ & Triple a b c};
}.
