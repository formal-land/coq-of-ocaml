Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition e_invalid {A B : Type} (x : A) : M [ OCaml.Invalid_argument ] B :=
  match x with
  | _ => OCaml.Pervasives.invalid_arg "error" % string
  end.

Definition e_failure {A B : Type} (x : A) : M [ OCaml.Failure ] B :=
  match x with
  | _ => OCaml.Pervasives.failwith "error" % string
  end.

Definition e_exit1 {A B : Type} (x : A) : M [ OCaml.Pervasives.Exit ] B :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.

Definition e_exit2 {A B : Type} (x : A) : M [ OCaml.Pervasives.Exit ] B :=
  match x with
  | _ => OCaml.Pervasives.raise_Exit tt
  end.

Definition b_eq : bool := equiv_decb 1 2.

Definition b_neq1 : bool := nequiv_decb true false.

Definition b_neq2 : bool := nequiv_decb tt tt.

Definition b_lt : bool := OCaml.Pervasives.lt 1 2.

Definition b_gt : bool := OCaml.Pervasives.gt 1 2.

Definition b_le : bool := OCaml.Pervasives.le true false.

Definition b_ge : bool := OCaml.Pervasives.ge tt tt.

Definition comp : Z := OCaml.Pervasives.compare 1 2.

Definition n_min : Z := OCaml.Pervasives.min 1 2.

Definition n_max : Z := OCaml.Pervasives.max 1 2.

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

Definition ss : string := String.append "begin" % string "end" % string.

Definition n_char : Z := OCaml.Pervasives.int_of_char "c" % char.

Definition char_n : ascii := OCaml.Pervasives.char_of_int 23.

Definition i : unit := OCaml.Pervasives.ignore 12.

Definition s_bool : string := OCaml.Pervasives.string_of_bool false.

Definition bool_s : bool := OCaml.Pervasives.bool_of_string "false" % string.

Definition s_n : string := OCaml.Pervasives.string_of_int 12.

Definition n_s : Z := OCaml.Pervasives.int_of_string "12" % string.

Definition n1 : Z := fst (12, 13).

Definition n2 : Z := snd (12, 13).

Definition ll : list Z :=
  OCaml.Pervasives.app (cons 1 (cons 2 [])) (cons 3 (cons 4 [])).

Definition p_c {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.print_char "c" % char
  end.

Definition p_s {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.print_string "str" % string
  end.

Definition p_n {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.print_int 12
  end.

Definition p_endline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.print_endline "str" % string
  end.

Definition p_newline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.print_newline tt
  end.

Definition perr_c {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.prerr_char "c" % char
  end.

Definition perr_s {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.prerr_string "str" % string
  end.

Definition perr_n {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.prerr_int 12
  end.

Definition perr_endline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.prerr_endline "str" % string
  end.

Definition perr_newline {A : Type} (x : A) : M [ IO ] unit :=
  match x with
  | _ => OCaml.Pervasives.prerr_newline tt
  end.

Definition r_s {A : Type} (x : A) : M [ IO ] string :=
  match x with
  | _ => OCaml.Pervasives.read_line tt
  end.

Definition r_n {A : Type} (x : A) : M [ IO ] Z :=
  match x with
  | _ => OCaml.Pervasives.read_int tt
  end.
