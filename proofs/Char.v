Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

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

#[global]
Instance strict_order : StrictOrder Lt.t :=
  {|
    StrictOrder_Irreflexive := Lt.irreflexivity;
    StrictOrder_Transitive := Lt.transitivity;
  |}.

#[global]
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
