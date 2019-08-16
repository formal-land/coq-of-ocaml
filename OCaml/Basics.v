Require Import Libraries.
Require Import Effect.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

(* TODO: add floats, add the different integer types (int32, int64, ...). *)
Class OrderDec {A R} `(StrictOrder A R) := {
  compare : A -> A -> comparison;
  compare_is_sound : forall x y,
    CompareSpec (x = y) (R x y) (R y x) (compare x y) }.

Module Unit.
  Definition lt (x y : unit) : Prop := False.

  Instance strict_order : StrictOrder lt.
    refine {|
      StrictOrder_Irreflexive := _;
      StrictOrder_Transitive := _ |}.
    - intro x.
      unfold complement, lt.
      trivial.
    - intros x y z Rxy Ryz.
      exact Rxy.
  Qed.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun x y => Eq;
      compare_is_sound := fun x y => CompEq _ _ _ |}.
    abstract (now destruct x; destruct y).
  Defined.
End Unit.

Module Bool.
  Inductive lt : bool -> bool -> Prop :=
  | lt_intro : lt false true.

  Instance strict_order : StrictOrder lt.
    refine {|
      StrictOrder_Irreflexive := _;
      StrictOrder_Transitive := _ |}.
    - intros x Hxx.
      inversion Hxx.
    - intros x y z Hxy Hyz.
      destruct Hxy; destruct Hyz.
      constructor.
  Qed.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun x y =>
        match (x, y) with
        | (false, true) => Lt
        | (false, false) | (true, true) => Eq
        | (true, false) => Gt
        end;
      compare_is_sound := fun x y => _ |}.
    abstract (destruct x; destruct y;
      try apply CompLt; try apply CompEq; try apply CompGt;
      constructor).
  Defined.
End Bool.

Module Z.
  Instance eq_dec : EqDec (eq_setoid Z) := Z.eq_dec.

  Instance order_dec : OrderDec Z.lt_strorder := {|
    compare := Z.compare;
    compare_is_sound := Z.compare_spec |}.
End Z.

(** OCaml functions are converted to their Coq's counter parts when it is
    possible. *)
Module Pervasives.
  (** * Comparisons *)
  Definition lt {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => false
    | Lt => true
    | Gt => false
    end.

  Definition gt {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => false
    | Lt => false
    | Gt => true
    end.

  Definition le {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => true
    | Lt => true
    | Gt => false
    end.

  Definition ge {A : Type} {R} `{OrderDec A R} (x y : A) : bool :=
    match compare x y with
    | Eq => true
    | Lt => false
    | Gt => true
    end.

  Definition min {A : Type} {R} `{OrderDec A R} (x y : A) : A :=
    match compare x y with
    | Eq => x
    | Lt => x
    | Gt => y
    end.

  Definition max {A : Type} {R} `{OrderDec A R} (x y : A) : A :=
    match compare x y with
    | Eq => x
    | Lt => y
    | Gt => x
    end.

  Definition compare {A : Type} {R} `{OrderDec A R} (x y : A) : Z :=
    match compare x y with
    | Eq => 0
    | Lt => -1
    | Gt => 1
    end.

  (** * Boolean operations *)

  (** * Composition operators *)
  Definition reverse_apply {A B : Type} (x : A) (f : A -> B) : B :=
    f x.

  (** * Integer arithmetic *)

  (** * Bitwise operations *)

  (** * Floating-point arithmetic *)
  (* TODO *)

  (** * String operations *)

  (** * Character operations *)
  Definition int_of_char (c : ascii) : Z :=
    Z.of_nat (nat_of_ascii c).

  (** * Unit operations *)
  Definition ignore {A : Type} (_ : A) : unit :=
    tt.

  (** * String conversion functions *)
  Definition string_of_bool (b : bool) : string :=
    if b then
      "true" % string
    else
      "false" % string.

  (* TODO *)
  Definition bool_of_string (s : string) : bool :=
    false.

  (* TODO *)
  Definition string_of_int (n : Z) : string :=
    "0" % string.

  (* TODO *)
  Definition int_of_string (s : string) : Z :=
    0.

  (** * Pair operations *)

  (** * List operations *)
  (** The concatenation of lists with an implicit parameter. *)
  Definition app {A : Type} (l1 l2 : list A) : list A :=
    app l1 l2.

  (** * Operations on format strings *)
  (* TODO *)
End Pervasives.

Module String.
  Definition length (s : string) : Z :=
    Z.of_nat (String.length s).

  (* TODO: raise an exception if n < 0. *)
  Definition get (s : string) (n : Z) : ascii :=
    match String.get (Z.to_nat n) s with
    | None => "?" % char
    | Some c => c
    end.

  Fixpoint _make (n : nat) (c : ascii) : string :=
    match n with
    | O => EmptyString
    | S n => String c (_make n c)
    end.

  (* TODO: raise an exception if n < 0. *)
  Definition make (n : Z) (c : ascii) : string :=
    _make (Z.to_nat n) c.

  (* TODO *)
  Definition sub (s : string) (start : Z) (length : Z) : string :=
    s.

  (* TODO *)
  Definition escaped (s : string) : string :=
    s.
End String.
