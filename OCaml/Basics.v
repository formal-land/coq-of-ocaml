Require Import ssr.ssrbool.
Require Import Libraries.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Inductive sigS (A : Type) (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

(** Conversion from a module to a first-class module. *)
Definition pack {A : Type} {P : A -> Set} (M : {x : A & P x}) : {x : A @ P x} :=
  let 'existT _ _ M := M in
  existS _ _ M.

Notation "(| record |)" := (projT2 record).

Module Primitive.
  Set Primitive Projections.

  Record prod {A B : Type} : Type := pair {
    fst : A;
    snd : B;
  }.
  Arguments prod : clear implicits.

  Unset Primitive Projections.
End Primitive.

Notation "[ X ** Y ** .. ** Z ]" :=
  (Primitive.prod .. (Primitive.prod X Y) .. Z) : type_scope.
Notation "[ x , y , .. , z ]" :=
  (Primitive.pair .. (Primitive.pair x y) .. z).

(* TODO: add floats, add the different integer types (int32, int64, ...). *)
Class OrderDec {A R} `(StrictOrder A R) := {
  compare : A -> A -> comparison;
  compare_is_sound : forall x y,
    CompareSpec (x = y) (R x y) (R y x) (compare x y) }.

Definition array (A : Set) : Set := list A.

Parameter axiom : forall {A : Set}, A.

Parameter assert : forall (A : Set), bool -> A.

Axiom obj_magic : forall {A : Set} (B : Set), A -> B.

Axiom obj_magic_exists : forall {A : Set} {Es : Type} (T : Es -> Set),
  A -> {vs : Es & T vs}.

Axiom obj_magic_eval : forall {A : Set} {x : A}, obj_magic A x = x.

Axiom obj_magic_exists_eval
  : forall {Es : Type} {T : Es -> Set} {vs : Es} {x : T vs},
  obj_magic_exists T x = existT _ vs x.

Parameter unreachable_gadt_branch : forall {A : Set}, A.

Parameter extensible_type : Set.

Parameter extensible_type_value : extensible_type.

Definition int := Z.

Definition float := Z.

Definition int32 := Z.

Definition int64 := Z.

Definition nativeint := Z.

Parameter try : forall {A : Set}, A -> A.

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
Module Stdlib.
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
End Stdlib.

Module Char.
  Module Lt.
    Definition t (c1 c2 : ascii) : Prop :=
      N.lt (N_of_ascii c1) (N_of_ascii c2).

    Lemma irreflexivity (c : ascii) : ~ t c c.
      apply N.lt_irrefl.
    Qed.

    Lemma transitivity (c1 c2 c3 : ascii) : t c1 c2 -> t c2 c3 -> t c1 c3.
      apply N.lt_trans.
    Qed.

    Lemma N_of_ascii_inj (c1 c2 : ascii) : N_of_ascii c1 = N_of_ascii c2 -> c1 = c2.
      intro H.
      rewrite <- (ascii_N_embedding c1).
      rewrite <- (ascii_N_embedding c2).
      rewrite H.
      reflexivity.
    Qed.
  End Lt.

  Instance strict_order : StrictOrder Lt.t :=
    {|
      StrictOrder_Irreflexive := Lt.irreflexivity;
      StrictOrder_Transitive := Lt.transitivity;
    |}.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun c1 c2 => (N_of_ascii c1 ?= N_of_ascii c2) % N;
      compare_is_sound := fun c1 c2 => _;
    |}.
    destruct (N.compare_spec (N_of_ascii c1) (N_of_ascii c2)) as [Heq | Hlt | Hgt];
      [apply CompEq | apply CompLt | apply CompGt].
    - now apply Lt.N_of_ascii_inj.
    - exact Hlt.
    - exact Hgt.
  Defined.
End Char.

Module Seq.
  Reserved Notation "'t".

  Inductive node (A : Set) : Set :=
  | Nil : node A
  | Cons : A -> 't A -> node A

  where "'t" := (fun (T : Set) => unit -> node T).

  Definition t := 't.

  Arguments Nil {_}.
  Arguments Cons {_}.
End Seq.

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

  Fixpoint concat (sep : string) (sl : list string) : string :=
    match sl with
    | [] => ""
    | [s] => s
    | s :: sl => String.append (String.append s sep) (concat sep sl)
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

  Module Lt.
    Inductive t : string -> string -> Prop :=
    | EmptyString : forall c s, t EmptyString (String c s)
    | StringStringLt : forall c1 s1 c2 s2,
      N.lt (N_of_ascii c1) (N_of_ascii c2) -> t (String c1 s1) (String c2 s2)
    | StringStringEq : forall c1 s1 c2 s2,
      c1 = c2 -> t s1 s2 -> t (String c1 s1) (String c2 s2).

    Fixpoint irreflexivity (s : string) (H : t s s) : False.
      inversion_clear H.
      - apply (Char.Lt.irreflexivity H0).
      - apply (irreflexivity _ H1).
    Qed.

    Fixpoint transitivity (s1 s2 s3 : string) (H12 : t s1 s2) (H23 : t s2 s3) : t s1 s3.
      inversion H12; inversion H23; try apply EmptyString; try congruence.
      - apply StringStringLt.
        apply N.lt_trans with (m := N_of_ascii c2); congruence.
      - apply StringStringLt; congruence.
      - apply StringStringLt; congruence.
      - apply StringStringEq; try congruence.
        replace s4 with s5 in * by congruence.
        now apply transitivity with (s2 := s5).
    Qed.
  End Lt.

  Fixpoint ltb (s1 s2 : string) : bool :=
    match s1, s2 with
   | EmptyString, EmptyString => false
   | EmptyString, String _ _ => true
   | String _ _, EmptyString => false
   | String c1 s1', String c2 s2' =>
    let n1 := N_of_ascii c1 in
    let n2 := N_of_ascii c2 in
    (N.ltb n1 n2 || (N.eqb n1 n2 && ltb s1' s2')) % bool
   end.

  Fixpoint ltb_spec (s1 s2 : string) : Bool.reflect (Lt.t s1 s2) (ltb s1 s2).
    destruct s1 as [| c1 s1]; destruct s2 as [| c2 s2]; simpl.
    - apply Bool.ReflectF.
      intro; now apply Lt.irreflexivity with (s := "" % string).
    - apply Bool.ReflectT.
      apply Lt.EmptyString.
    - apply Bool.ReflectF.
      intro H; inversion H.
    - case_eq ((N_of_ascii c1 <? N_of_ascii c2)%N); intro H_lt; simpl.
      + apply Bool.ReflectT.
        apply Lt.StringStringLt.
        now apply N.ltb_lt.
      + case_eq ((N_of_ascii c1 =? N_of_ascii c2)%N); intro H_eq; simpl.
        * destruct (ltb_spec s1 s2); constructor.
          -- apply Lt.StringStringEq; trivial.
             apply Char.Lt.N_of_ascii_inj.
             now apply N.eqb_eq.
          -- intro H; inversion H; try tauto.
             assert ((N_of_ascii c1 <? N_of_ascii c2)%N = true) by
               now apply N.ltb_lt.
             congruence.
        * apply Bool.ReflectF.
          intro H; inversion H.
          -- assert ((N_of_ascii c1 <? N_of_ascii c2)%N = true) by
               now apply N.ltb_lt.
             congruence.
          -- assert ((N_of_ascii c1 =? N_of_ascii c2)%N = true) by
               (apply N.eqb_eq; congruence).
             congruence.
  Qed.

  Fixpoint ltb_or_eqb_or_gtb
    (s1 s2 : string)
    (H_nltb : ltb s1 s2 = false)
    (H_neqb : String.eqb s1 s2 = false)
    : ltb s2 s1 = true.
    destruct s1 as [| c1 s1]; destruct s2 as [| c2 s2]; simpl in *; try congruence.
    destruct (Bool.orb_false_elim _ _ H_nltb) as [H_c1c2 H].
    case_eq ((N_of_ascii c1 ?= N_of_ascii c2)%N); intro H_comp_c1c2.
    - assert (H_eq_c1c2 : N_of_ascii c1 = N_of_ascii c2) by
        now apply N.compare_eq_iff.
      replace ((N_of_ascii c2 =? N_of_ascii c1)%N) with true by (
        symmetry;
        apply N.eqb_eq;
        congruence
      ).
      rewrite ltb_or_eqb_or_gtb.
      + apply Bool.orb_true_r.
      + destruct (proj1 (Bool.andb_false_iff _ _) H); trivial.
        assert (H_eq_c1c2_bis := proj2 (N.eqb_eq _ _) H_eq_c1c2).
        congruence.
      + assert (H_eqb_c1c2 : (c1 =? c2)%char = true) by (
          apply Ascii.eqb_eq;
          now apply Char.Lt.N_of_ascii_inj
        ).
        now rewrite H_eqb_c1c2 in H_neqb.
    - assert ((N_of_ascii c1 <? N_of_ascii c2)%N = true) by (
        apply N.ltb_lt;
        now apply N.compare_lt_iff
      ).
      congruence.
    - assert (H_gt_c1c2 : (N_of_ascii c2 < N_of_ascii c1) % N) by
        now apply N.compare_gt_iff.
      now rewrite (proj2 (N.ltb_lt _ _) H_gt_c1c2).
  Qed.

  Instance strict_order : StrictOrder Lt.t := {|
      StrictOrder_Irreflexive := Lt.irreflexivity;
      StrictOrder_Transitive := Lt.transitivity;
    |}.

  Instance order_dec : OrderDec strict_order.
    refine {|
      compare := fun s1 s2 =>
        if String.eqb s1 s2 then
          Eq
        else if ltb s1 s2 then
          Lt
        else
          Gt;
      compare_is_sound := fun s1 s2 => _;
    |}.
    case_eq (String.eqb s1 s2); intro H_eq.
    - apply CompEq.
      now apply String.eqb_eq.
    - case_eq (ltb s1 s2); intro H_lt.
      + apply CompLt.
        apply (ltb_spec _ _ H_lt).
      + apply CompGt.
        apply (ltb_spec _ _ (ltb_or_eqb_or_gtb _ _ H_lt H_eq)).
  Defined.
End String.

Module CamlinternalFormatBasics.
  Inductive padty : Set :=
  | Left : padty
  | Right : padty
  | Zeros : padty.

  Inductive int_conv : Set :=
  | Int_d : int_conv
  | Int_pd : int_conv
  | Int_sd : int_conv
  | Int_i : int_conv
  | Int_pi : int_conv
  | Int_si : int_conv
  | Int_x : int_conv
  | Int_Cx : int_conv
  | Int_X : int_conv
  | Int_CX : int_conv
  | Int_o : int_conv
  | Int_Co : int_conv
  | Int_u : int_conv.

  Inductive float_conv : Set :=
  | Float_f : float_conv
  | Float_pf : float_conv
  | Float_sf : float_conv
  | Float_e : float_conv
  | Float_pe : float_conv
  | Float_se : float_conv
  | Float_E : float_conv
  | Float_pE : float_conv
  | Float_sE : float_conv
  | Float_g : float_conv
  | Float_pg : float_conv
  | Float_sg : float_conv
  | Float_G : float_conv
  | Float_pG : float_conv
  | Float_sG : float_conv
  | Float_F : float_conv
  | Float_h : float_conv
  | Float_ph : float_conv
  | Float_sh : float_conv
  | Float_H : float_conv
  | Float_pH : float_conv
  | Float_sH : float_conv.

  Definition char_set : Set := string.

  Inductive counter : Set :=
  | Line_counter : counter
  | Char_counter : counter
  | Token_counter : counter.

  Reserved Notation "'padding".

  Inductive padding_gadt : Set :=
  | No_padding_gadt : padding_gadt
  | Lit_padding_gadt : padty -> int -> padding_gadt
  | Arg_padding_gadt : padty -> padding_gadt

  where "'padding" := (fun (_ _ : Set) => padding_gadt).

  Definition padding := 'padding.

  Definition No_padding {a : Set} : padding a a := No_padding_gadt.
  Definition Lit_padding {a : Set} : padty -> int -> padding a a :=
    Lit_padding_gadt.
  Definition Arg_padding {a : Set} : padty -> padding (int -> a) a :=
    Arg_padding_gadt.

  Definition pad_option : Set := option int.

  Reserved Notation "'precision".

  Inductive precision_gadt : Set :=
  | No_precision_gadt : precision_gadt
  | Lit_precision_gadt : int -> precision_gadt
  | Arg_precision_gadt : precision_gadt

  where "'precision" := (fun (_ _ : Set) => precision_gadt).

  Definition precision := 'precision.

  Definition No_precision {a : Set} : precision a a := No_precision_gadt.
  Definition Lit_precision {a : Set} : int -> precision a a := Lit_precision_gadt.
  Definition Arg_precision {a : Set} : precision (int -> a) a :=
    Arg_precision_gadt.

  Definition prec_option : Set := option int.

  Reserved Notation "'custom_arity".

  Inductive custom_arity_gadt : Set :=
  | Custom_zero_gadt : custom_arity_gadt
  | Custom_succ_gadt : custom_arity_gadt -> custom_arity_gadt

  where "'custom_arity" := (fun (_ _ _ : Set) => custom_arity_gadt).

  Definition custom_arity := 'custom_arity.

  Definition Custom_zero {a : Set} : custom_arity a string a := Custom_zero_gadt.
  Definition Custom_succ {a b c x : Set} :
    custom_arity a b c -> custom_arity a (x -> b) (x -> c) := Custom_succ_gadt.

  Inductive block_type : Set :=
  | Pp_hbox : block_type
  | Pp_vbox : block_type
  | Pp_hvbox : block_type
  | Pp_hovbox : block_type
  | Pp_box : block_type
  | Pp_fits : block_type.

  Inductive formatting_lit : Set :=
  | Close_box : formatting_lit
  | Close_tag : formatting_lit
  | Break : string -> int -> int -> formatting_lit
  | FFlush : formatting_lit
  | Force_newline : formatting_lit
  | Flush_newline : formatting_lit
  | Magic_size : string -> int -> formatting_lit
  | Escaped_at : formatting_lit
  | Escaped_percent : formatting_lit
  | Scan_indic : ascii -> formatting_lit.

  Reserved Notation "'formatting_gen".
  Reserved Notation "'fmtty_rel".
  Reserved Notation "'fmtty".
  Reserved Notation "'fmt".
  Reserved Notation "'ignored".
  Reserved Notation "'format6".

  Inductive formatting_gen_gadt : Set :=
  | Open_tag_gadt : forall {a b c d e f : Set},
    'format6 a b c d e f -> formatting_gen_gadt
  | Open_box_gadt : forall {a b c d e f : Set},
    'format6 a b c d e f -> formatting_gen_gadt

  with fmtty_rel_gadt : Set :=
  | Char_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | String_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Int_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Int32_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Nativeint_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Int64_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Float_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Bool_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Format_arg_ty_gadt : forall {g h i j k l : Set},
    'fmtty g h i j k l -> fmtty_rel_gadt -> fmtty_rel_gadt
  | Format_subst_ty_gadt :
    fmtty_rel_gadt -> fmtty_rel_gadt -> fmtty_rel_gadt -> fmtty_rel_gadt
  | Alpha_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Theta_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Any_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Reader_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | Ignored_reader_ty_gadt : fmtty_rel_gadt -> fmtty_rel_gadt
  | End_of_fmtty_gadt : fmtty_rel_gadt

  with fmt_gadt : Set :=
  | Char_gadt : fmt_gadt -> fmt_gadt
  | Caml_char_gadt : fmt_gadt -> fmt_gadt
  | String_gadt : forall {a x : Set},
    padding x (string -> a) -> fmt_gadt -> fmt_gadt
  | Caml_string_gadt : forall {a x : Set},
    padding x (string -> a) -> fmt_gadt -> fmt_gadt
  | Int_gadt : forall {a x y : Set},
    int_conv -> padding x y -> precision y (int -> a) -> fmt_gadt -> fmt_gadt
  | Int32_gadt : forall {a x y : Set},
    int_conv -> padding x y -> precision y (int32 -> a) -> fmt_gadt -> fmt_gadt
  | Nativeint_gadt : forall {a x y : Set},
    int_conv -> padding x y -> precision y (nativeint -> a) -> fmt_gadt ->
    fmt_gadt
  | Int64_gadt : forall {a x y : Set},
    int_conv -> padding x y -> precision y (int64 -> a) -> fmt_gadt -> fmt_gadt
  | Float_gadt : forall {a x y : Set},
    float_conv -> padding x y -> precision y (float -> a) -> fmt_gadt -> fmt_gadt
  | Bool_gadt : forall {a x : Set}, padding x (bool -> a) -> fmt_gadt -> fmt_gadt
  | Flush_gadt : fmt_gadt -> fmt_gadt
  | String_literal_gadt : string -> fmt_gadt -> fmt_gadt
  | Char_literal_gadt : ascii -> fmt_gadt -> fmt_gadt
  | Format_arg_gadt : forall {g h i j k l : Set},
    pad_option -> 'fmtty g h i j k l -> fmt_gadt -> fmt_gadt
  | Format_subst_gadt : forall {a b c d g g2 h i j j2 k l : Set},
    pad_option -> 'fmtty_rel g h i j k l g2 b c j2 d a -> fmt_gadt -> fmt_gadt
  | Alpha_gadt : fmt_gadt -> fmt_gadt
  | Theta_gadt : fmt_gadt -> fmt_gadt
  | Formatting_lit_gadt : formatting_lit -> fmt_gadt -> fmt_gadt
  | Formatting_gen_gadt : forall {a1 b c d1 e1 f1 : Set},
    'formatting_gen a1 b c d1 e1 f1 -> fmt_gadt -> fmt_gadt
  | Reader_gadt : fmt_gadt -> fmt_gadt
  | Scan_char_set_gadt : pad_option -> char_set -> fmt_gadt -> fmt_gadt
  | Scan_get_counter_gadt : counter -> fmt_gadt -> fmt_gadt
  | Scan_next_char_gadt : fmt_gadt -> fmt_gadt
  | Ignored_param_gadt : forall {a b c d x y : Set},
    'ignored a b c d y x -> fmt_gadt -> fmt_gadt
  | Custom_gadt : forall {a x y : Set},
    custom_arity a x y -> (unit -> x) -> fmt_gadt -> fmt_gadt
  | End_of_format_gadt : fmt_gadt

  with ignored_gadt : Set :=
  | Ignored_char_gadt : ignored_gadt
  | Ignored_caml_char_gadt : ignored_gadt
  | Ignored_string_gadt : pad_option -> ignored_gadt
  | Ignored_caml_string_gadt : pad_option -> ignored_gadt
  | Ignored_int_gadt : int_conv -> pad_option -> ignored_gadt
  | Ignored_int32_gadt : int_conv -> pad_option -> ignored_gadt
  | Ignored_nativeint_gadt : int_conv -> pad_option -> ignored_gadt
  | Ignored_int64_gadt : int_conv -> pad_option -> ignored_gadt
  | Ignored_float_gadt : pad_option -> prec_option -> ignored_gadt
  | Ignored_bool_gadt : pad_option -> ignored_gadt
  | Ignored_format_arg_gadt : forall {g h i j k l : Set},
    pad_option -> 'fmtty g h i j k l -> ignored_gadt
  | Ignored_format_subst_gadt : forall {a b c d e f : Set},
    pad_option -> 'fmtty a b c d e f -> ignored_gadt
  | Ignored_reader_gadt : ignored_gadt
  | Ignored_scan_char_set_gadt : pad_option -> char_set -> ignored_gadt
  | Ignored_scan_get_counter_gadt : counter -> ignored_gadt
  | Ignored_scan_next_char_gadt : ignored_gadt

  with format6_gadt : Set :=
  | Format_gadt : forall {a b c d e f : Set},
    'fmt a b c d e f -> string -> format6_gadt

  where "'formatting_gen" := (fun (_ _ _ _ _ _ : Set) => formatting_gen_gadt)
  and "'fmtty_rel" := (fun (_ _ _ _ _ _ _ _ _ _ _ _ : Set) => fmtty_rel_gadt)
  and "'fmtty" := (fun (t_a t_b t_c t_d t_e t_f : Set) =>
    'fmtty_rel t_a t_b t_c t_d t_e t_f t_a t_b t_c t_d t_e t_f)
  and "'fmt" := (fun (_ _ _ _ _ _ : Set) => fmt_gadt)
  and "'ignored" := (fun (_ _ _ _ _ _ : Set) => ignored_gadt)
  and "'format6" := (fun (_ _ _ _ _ _ : Set) => format6_gadt).

  Definition formatting_gen := 'formatting_gen.
  Definition fmtty_rel := 'fmtty_rel.
  Definition fmtty := 'fmtty.
  Definition fmt := 'fmt.
  Definition ignored := 'ignored.
  Definition format6 := 'format6.

  Definition Open_tag {a b c d e f : Set} :
    format6 a b c d e f -> formatting_gen a b c d e f := Open_tag_gadt (a := a)
    (b := b) (c := c) (d := d) (e := e) (f := f).
  Definition Open_box {a b c d e f : Set} :
    format6 a b c d e f -> formatting_gen a b c d e f := Open_box_gadt (a := a)
    (b := b) (c := c) (d := d) (e := e) (f := f).
  Definition Char_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (ascii -> a1) b1 c1 d1 e1 f1 (ascii -> a2) b2 c2 d2 e2 f2 :=
    Char_ty_gadt.
  Definition String_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (string -> a1) b1 c1 d1 e1 f1 (string -> a2) b2 c2 d2 e2 f2 :=
    String_ty_gadt.
  Definition Int_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (int -> a1) b1 c1 d1 e1 f1 (int -> a2) b2 c2 d2 e2 f2 :=
    Int_ty_gadt.
  Definition Int32_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (int32 -> a1) b1 c1 d1 e1 f1 (int32 -> a2) b2 c2 d2 e2 f2 :=
    Int32_ty_gadt.
  Definition Nativeint_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (nativeint -> a1) b1 c1 d1 e1 f1 (nativeint -> a2) b2 c2 d2 e2 f2 :=
    Nativeint_ty_gadt.
  Definition Int64_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (int64 -> a1) b1 c1 d1 e1 f1 (int64 -> a2) b2 c2 d2 e2 f2 :=
    Int64_ty_gadt.
  Definition Float_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (float -> a1) b1 c1 d1 e1 f1 (float -> a2) b2 c2 d2 e2 f2 :=
    Float_ty_gadt.
  Definition Bool_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (bool -> a1) b1 c1 d1 e1 f1 (bool -> a2) b2 c2 d2 e2 f2 :=
    Bool_ty_gadt.
  Definition Format_arg_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g h i j k l : Set}
    :
    fmtty g h i j k l -> fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (format6 g h i j k l -> a1) b1 c1 d1 e1 f1
      (format6 g h i j k l -> a2) b2 c2 d2 e2 f2 := Format_arg_ty_gadt (g := g)
    (h := h) (i := i) (j := j) (k := k) (l := l).
  Definition Format_subst_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g g1 g2 h i j j1
    j2 k l : Set} :
    fmtty_rel g h i j k l g1 b1 c1 j1 d1 a1 ->
    fmtty_rel g h i j k l g2 b2 c2 j2 d2 a2 ->
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (format6 g h i j k l -> g1) b1 c1 j1 e1 f1
      (format6 g h i j k l -> g2) b2 c2 j2 e2 f2 := Format_subst_ty_gadt.
  Definition Alpha_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 x : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel ((b1 -> x -> c1) -> x -> a1) b1 c1 d1 e1 f1
      ((b2 -> x -> c2) -> x -> a2) b2 c2 d2 e2 f2 := Alpha_ty_gadt.
  Definition Theta_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel ((b1 -> c1) -> a1) b1 c1 d1 e1 f1 ((b2 -> c2) -> a2) b2 c2 d2 e2 f2
    := Theta_ty_gadt.
  Definition Any_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 x : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (x -> a1) b1 c1 d1 e1 f1 (x -> a2) b2 c2 d2 e2 f2 := Any_ty_gadt.
  Definition Reader_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 x : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel (x -> a1) b1 c1 ((b1 -> x) -> d1) e1 f1 (x -> a2) b2 c2
      ((b2 -> x) -> d2) e2 f2 := Reader_ty_gadt.
  Definition Ignored_reader_ty {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 x : Set} :
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel a1 b1 c1 ((b1 -> x) -> d1) e1 f1 a2 b2 c2 ((b2 -> x) -> d2) e2 f2 :=
    Ignored_reader_ty_gadt.
  Definition End_of_fmtty {b1 b2 c1 c2 d1 d2 f1 f2 : Set} :
    fmtty_rel f1 b1 c1 d1 d1 f1 f2 b2 c2 d2 d2 f2 := End_of_fmtty_gadt.
  Definition Char {a b c d e f : Set} :
    fmt a b c d e f -> fmt (ascii -> a) b c d e f := Char_gadt.
  Definition Caml_char {a b c d e f : Set} :
    fmt a b c d e f -> fmt (ascii -> a) b c d e f := Caml_char_gadt.
  Definition String {a b c d e f x : Set} :
    padding x (string -> a) -> fmt a b c d e f -> fmt x b c d e f := String_gadt
    (a := a) (x := x).
  Definition Caml_string {a b c d e f x : Set} :
    padding x (string -> a) -> fmt a b c d e f -> fmt x b c d e f :=
    Caml_string_gadt (a := a) (x := x).
  Definition Int {a b c d e f x y : Set} :
    int_conv -> padding x y -> precision y (int -> a) -> fmt a b c d e f ->
    fmt x b c d e f := Int_gadt (a := a) (x := x) (y := y).
  Definition Int32 {a b c d e f x y : Set} :
    int_conv -> padding x y -> precision y (int32 -> a) -> fmt a b c d e f ->
    fmt x b c d e f := Int32_gadt (a := a) (x := x) (y := y).
  Definition Nativeint {a b c d e f x y : Set} :
    int_conv -> padding x y -> precision y (nativeint -> a) -> fmt a b c d e f ->
    fmt x b c d e f := Nativeint_gadt (a := a) (x := x) (y := y).
  Definition Int64 {a b c d e f x y : Set} :
    int_conv -> padding x y -> precision y (int64 -> a) -> fmt a b c d e f ->
    fmt x b c d e f := Int64_gadt (a := a) (x := x) (y := y).
  Definition Float {a b c d e f x y : Set} :
    float_conv -> padding x y -> precision y (float -> a) -> fmt a b c d e f ->
    fmt x b c d e f := Float_gadt (a := a) (x := x) (y := y).
  Definition Bool {a b c d e f x : Set} :
    padding x (bool -> a) -> fmt a b c d e f -> fmt x b c d e f := Bool_gadt
    (a := a) (x := x).
  Definition Flush {a b c d e f : Set} : fmt a b c d e f -> fmt a b c d e f :=
    Flush_gadt.
  Definition String_literal {a b c d e f : Set} :
    string -> fmt a b c d e f -> fmt a b c d e f := String_literal_gadt.
  Definition Char_literal {a b c d e f : Set} :
    ascii -> fmt a b c d e f -> fmt a b c d e f := Char_literal_gadt.
  Definition Format_arg {a b c d e f g h i j k l : Set} :
    pad_option -> fmtty g h i j k l -> fmt a b c d e f ->
    fmt (format6 g h i j k l -> a) b c d e f := Format_arg_gadt (g := g) (h := h)
    (i := i) (j := j) (k := k) (l := l).
  Definition Format_subst {a b c d e f g g2 h i j j2 k l : Set} :
    pad_option -> fmtty_rel g h i j k l g2 b c j2 d a -> fmt a b c d e f ->
    fmt (format6 g h i j k l -> g2) b c j2 e f := Format_subst_gadt (a := a)
    (b := b) (c := c) (d := d) (g := g) (g2 := g2) (h := h) (i := i) (j := j)
    (j2 := j2) (k := k) (l := l).
  Definition Alpha {a b c d e f x : Set} :
    fmt a b c d e f -> fmt ((b -> x -> c) -> x -> a) b c d e f := Alpha_gadt.
  Definition Theta {a b c d e f : Set} :
    fmt a b c d e f -> fmt ((b -> c) -> a) b c d e f := Theta_gadt.
  Definition Formatting_lit {a b c d e f : Set} :
    formatting_lit -> fmt a b c d e f -> fmt a b c d e f := Formatting_lit_gadt.
  Definition Formatting_gen {a1 b c d1 e1 e2 f1 f2 : Set} :
    formatting_gen a1 b c d1 e1 f1 -> fmt f1 b c e1 e2 f2 -> fmt a1 b c d1 e2 f2
    := Formatting_gen_gadt (a1 := a1) (b := b) (c := c) (d1 := d1) (e1 := e1)
    (f1 := f1).
  Definition Reader {a b c d e f x : Set} :
    fmt a b c d e f -> fmt (x -> a) b c ((b -> x) -> d) e f := Reader_gadt.
  Definition Scan_char_set {a b c d e f : Set} :
    pad_option -> char_set -> fmt a b c d e f -> fmt (string -> a) b c d e f :=
    Scan_char_set_gadt.
  Definition Scan_get_counter {a b c d e f : Set} :
    counter -> fmt a b c d e f -> fmt (int -> a) b c d e f :=
    Scan_get_counter_gadt.
  Definition Scan_next_char {a b c d e f : Set} :
    fmt a b c d e f -> fmt (ascii -> a) b c d e f := Scan_next_char_gadt.
  Definition Ignored_param {a b c d e f x y : Set} :
    ignored a b c d y x -> fmt x b c y e f -> fmt a b c d e f :=
    Ignored_param_gadt (a := a) (b := b) (c := c) (d := d) (x := x) (y := y).
  Definition Custom {a b c d e f x y : Set} :
    custom_arity a x y -> (unit -> x) -> fmt a b c d e f -> fmt y b c d e f :=
    Custom_gadt (a := a) (x := x) (y := y).
  Definition End_of_format {b c e f : Set} : fmt f b c e e f :=
    End_of_format_gadt.
  Definition Ignored_char {a b c d : Set} : ignored a b c d d a :=
    Ignored_char_gadt.
  Definition Ignored_caml_char {a b c d : Set} : ignored a b c d d a :=
    Ignored_caml_char_gadt.
  Definition Ignored_string {a b c d : Set} : pad_option -> ignored a b c d d a :=
    Ignored_string_gadt.
  Definition Ignored_caml_string {a b c d : Set} :
    pad_option -> ignored a b c d d a := Ignored_caml_string_gadt.
  Definition Ignored_int {a b c d : Set} :
    int_conv -> pad_option -> ignored a b c d d a := Ignored_int_gadt.
  Definition Ignored_int32 {a b c d : Set} :
    int_conv -> pad_option -> ignored a b c d d a := Ignored_int32_gadt.
  Definition Ignored_nativeint {a b c d : Set} :
    int_conv -> pad_option -> ignored a b c d d a := Ignored_nativeint_gadt.
  Definition Ignored_int64 {a b c d : Set} :
    int_conv -> pad_option -> ignored a b c d d a := Ignored_int64_gadt.
  Definition Ignored_float {a b c d : Set} :
    pad_option -> prec_option -> ignored a b c d d a := Ignored_float_gadt.
  Definition Ignored_bool {a b c d : Set} : pad_option -> ignored a b c d d a :=
    Ignored_bool_gadt.
  Definition Ignored_format_arg {a b c d g h i j k l : Set} :
    pad_option -> fmtty g h i j k l -> ignored a b c d d a :=
    Ignored_format_arg_gadt (g := g) (h := h) (i := i) (j := j) (k := k) (l := l).
  Definition Ignored_format_subst {a b c d e f : Set} :
    pad_option -> fmtty a b c d e f -> ignored a b c d e f :=
    Ignored_format_subst_gadt (a := a) (b := b) (c := c) (d := d) (e := e)
    (f := f).
  Definition Ignored_reader {a b c d x : Set} : ignored a b c ((b -> x) -> d) d a
    := Ignored_reader_gadt.
  Definition Ignored_scan_char_set {a b c d : Set} :
    pad_option -> char_set -> ignored a b c d d a := Ignored_scan_char_set_gadt.
  Definition Ignored_scan_get_counter {a b c d : Set} :
    counter -> ignored a b c d d a := Ignored_scan_get_counter_gadt.
  Definition Ignored_scan_next_char {a b c d : Set} : ignored a b c d d a :=
    Ignored_scan_next_char_gadt.
  Definition Format {a b c d e f : Set} :
    fmt a b c d e f -> string -> format6 a b c d e f := Format_gadt (a := a)
    (b := b) (c := c) (d := d) (e := e) (f := f).

  Parameter concat_fmtty : forall
    {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 g1 g2 j1 j2 : Set},
    fmtty_rel g1 b1 c1 j1 d1 a1 g2 b2 c2 j2 d2 a2 ->
    fmtty_rel a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 ->
    fmtty_rel g1 b1 c1 j1 e1 f1 g2 b2 c2 j2 e2 f2.

  Parameter erase_rel : forall {a b c d e f g h i j k l : Set},
    fmtty_rel a b c d e f g h i j k l -> fmtty a b c d e f.

  Parameter concat_fmt : forall {a b c d e f g h : Set},
    fmt a b c d e f -> fmt f b c e g h -> fmt a b c d g h.
End CamlinternalFormatBasics.
