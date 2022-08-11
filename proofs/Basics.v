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

Axiom cast : forall {A : Set} (B : Set), A -> B.

Axiom cast_exists : forall {A : Set} {Es : Type} (T : Es -> Set),
  A -> {vs : Es & T vs}.

Axiom cast_eval : forall {A : Set} {x : A}, cast A x = x.

Axiom cast_exists_eval_eq
  : forall {A : Set} {Es : Type} {T : Es -> Set} {vs : Es} {x : A}
  (H_eq : A = T vs),
  cast_exists (A := A) (Es := Es) T x =
  existT T vs (eq_rect (A := Set) A (fun x => x) x (T vs) H_eq).

Ltac rewrite_cast_exists_eval_eq vs :=
  match goal with
  | [ |- context[cast_exists ?T _] ] =>
    rewrite (cast_exists_eval_eq (T := T) (vs := vs) eq_refl);
    simpl
  end.

Parameter unreachable_gadt_branch : forall {A : Set}, A.

Parameter unreachable : forall {A : Set}, A.

(** Mutation of a record field. *)
Parameter set_record_field : forall {A B : Set}, A -> string -> B -> unit.

Inductive extensible_type : Set :=
| Build_extensible : string -> forall (A : Set), A -> extensible_type.
Arguments Build_extensible : clear implicits.

(** For backward compatibility. *)
Parameter extensible_type_value : extensible_type.

(** Polymorphic variants. *)
Module Variant.
  Inductive t : Set :=
  | Build : string -> forall (A : Set), A -> t.

  Arguments Build : clear implicits.
End Variant.

Parameter Set_oracle : string -> Set.

Axiom Set_oracle_invoke
  : forall {name : string} (A : Set),
    Set_oracle name = A.

Definition exn : Set := extensible_type.

Definition int := Z.

Definition float := Z.

Definition int32 := Z.

Definition int64 := Z.

Definition nativeint := Z.

Definition char := ascii.

Definition bytes := string.

Definition try {A : Set} (x : A) : A := x.

Definition try_with {A : Set} (e : unit -> A) (_with : extensible_type -> A)
  : A :=
  e tt.

Module Unit.
  Definition lt (x y : unit) : Prop := False.

  #[global]
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

  #[global]
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

  #[global]
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

  #[global]
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
  #[global]
  Instance eq_dec : EqDec (eq_setoid Z) := Z.eq_dec.

  #[global]
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
End Stdlib.

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
