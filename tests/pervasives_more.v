Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition b_eq : bool := equiv_decb 1 2.

Definition b_neq1 : bool := nequiv_decb true false.

Definition b_neq2 : bool := nequiv_decb tt tt.

Definition b_lt : bool := CoqOfOCaml.Stdlib.lt 1 2.

Definition b_gt : bool := CoqOfOCaml.Stdlib.gt 1 2.

Definition b_le : bool := CoqOfOCaml.Stdlib.le true false.

Definition b_ge : bool := CoqOfOCaml.Stdlib.ge tt tt.

Definition comp : int := CoqOfOCaml.Stdlib.compare 1 2.

Definition n_min : int := CoqOfOCaml.Stdlib.min 1 2.

Definition n_max : int := CoqOfOCaml.Stdlib.max 1 2.

Definition b_not : bool := negb false.

Definition b_and : bool := andb true false.

Definition b_or : bool := orb true false.

Definition app1 : int := (fun x => x) 12.

Definition app2 : int := (fun x => x) 12.

Definition n_neg1 : int := Z.opp 12.

Definition n_neg2 : int := (-12).

Definition n_pos1 : int := 12.

Definition n_pos2 : int := 12.

Definition n_succ : int := Z.succ 1.

Definition n_pred : int := Z.pred 1.

Definition n_plus : int := Z.add 1 2.

Definition n_minus : int := Z.sub 1 2.

Definition n_times : int := Z.mul 1 2.

Definition n_div : int := Z.div 1 2.

Definition n_mod : int := Z.modulo 1 2.

Definition n_abs : int := Z.abs 1.

Definition n_land : int := Z.land 12 13.

Definition n_lor : int := Z.lor 12 13.

Definition n_lxor : int := Z.lxor 12 13.

Definition n_lsl : int := Z.shiftl 12 13.

Definition n_lsr : int := Z.shiftr 12 13.

Definition ss : string := String.append "begin" "end".

Definition n_char : int := CoqOfOCaml.Stdlib.int_of_char "c" % char.

Definition i : unit := CoqOfOCaml.Stdlib.ignore 12.

Definition s_bool : string := CoqOfOCaml.Stdlib.string_of_bool false.

Definition bool_s : bool := CoqOfOCaml.Stdlib.bool_of_string "false".

Definition s_n : string := CoqOfOCaml.Stdlib.string_of_int 12.

Definition n_s : int := CoqOfOCaml.Stdlib.int_of_string "12".

Definition n1 : int := fst (12, 13).

Definition n2 : int := snd (12, 13).

Definition ll : list int := CoqOfOCaml.Stdlib.app [ 1; 2 ] [ 3; 4 ].
