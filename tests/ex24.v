Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition e_invalid {A B : Type} (x : B) : M [ OCaml.Invalid_argument ] A :=
  match x with
  | _ => OCaml.Pervasives.invalid_arg "error" % string
  end.

Definition e_failure {A B : Type} (x : B) : M [ OCaml.Failure ] A :=
  match x with
  | _ => OCaml.Pervasives.failwith "error" % string
  end.

Definition e_exit1 {A B : Type} (x : B) : M [ OCaml.Pervasives.Exit ] A :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.

Definition e_exit2 {A B : Type} (x : B) : M [ OCaml.Pervasives.Exit ] A :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.

Definition b_eq : bool := equiv_decb 1 2.

Definition b_neq : bool := nequiv_decb 1 2.

Definition b_not : bool := negb false.

Definition b_and : bool := andb true false.

Definition b_and_old : bool := andb true false.

Definition b_or : bool := orb true false.

Definition b_or_old : bool := orb true false.

Definition app1 : Z := OCaml.Pervasives.reverse_apply 12 (fun x => x).

Definition app2 : Z := apply (fun x => x) 12.

Definition n_neg1 : Z := Z.opp 12.

Definition n_neg2 : Z := (-12).

Definition n_pos1 : Z := 12.

Definition n_pos2 : Z := 12.

Definition n_succ : Z := Z.succ 1.

Definition n_pred : Z := Z.pred 1.

Definition n_plus : Z := Z.add 1 2.

Definition n_minus : Z := Z.sub 1 2.

Definition n_times : Z := Z.mul 1 2.

Definition n_div : Z := Z.div 1 2.

Definition n_mod : Z := Z.modulo 1 2.

Definition n_abs : Z := Z.abs 1.

Definition n_land : Z := Z.land 12 13.

Definition n_lor : Z := Z.lor 12 13.

Definition n_lxor : Z := Z.lxor 12 13.

Definition n_lsl : Z := Z.shiftl 12 13.

Definition n_lsr : Z := Z.shiftr 12 13.

Definition x : Z := 2.
