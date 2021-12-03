Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition b_value : bool :=
  orb (equiv_decb false true) (andb (nequiv_decb tt tt) (negb true)).

Definition n1 : int := Z.add 1 (Z.mul 2 3).

Definition n2 : int :=
  Z.sub (Z.add (Z.abs (-1)) 1) (Z.mul (Z.modulo (Z.div 5 23) 4) 3).

Definition n3 : int := Z.pred (Z.succ 12).

Definition n4 : int := Z.lxor (Z.lor (Z.land 5 7) 3) 9.

Definition n5 : int := Z.add (Z.shiftl 156 4) (Z.shiftr 12 1).

Definition s_value : string := String.append "ghj" "klm".

Definition c_value : int := CoqOfOCaml.Stdlib.int_of_char "c" % char.

Definition x_value : unit := CoqOfOCaml.Stdlib.ignore 23.

Definition p_value : int := Z.add (fst (1, 2)) (snd (3, 4)).

Definition l_value : list int := CoqOfOCaml.Stdlib.app [ 1; 2 ] [ 3 ].

Definition y_value : int := (fun (n_value : int) => Z.add n_value 1) 12.
