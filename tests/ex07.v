Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition b : bool :=
  orb (equiv_decb false true) (andb (nequiv_decb tt tt) (negb true)).

Definition n1 : Z := Z.add 1 (Z.mul 2 3).

Definition n2 : Z :=
  Z.sub (Z.add (Z.abs (-1)) 1) (Z.mul (Z.modulo (Z.div 5 23) 4) 3).

Definition n3 : Z := Z.pred (Z.succ 12).

Definition n4 : Z := Z.lxor (Z.lor (Z.land 5 7) 3) 9.

Definition n5 : Z := Z.add (Z.shiftl 156 4) (Z.shiftr 12 1).

Definition s : string := String.append "ghj" % string "klm" % string.

Definition c {A : Type} (x : A) : M [ OCaml.Invalid_argument ] ascii :=
  match x with
  | _ =>
    OCaml.Pervasives.char_of_int
      (Z.add (OCaml.Pervasives.int_of_char "c" % char) 1)
  end.

Definition x : unit := OCaml.Pervasives.ignore 23.

Definition p : Z := Z.add (fst (1, 2)) (snd (3, 4)).

Definition l : list Z := OCaml.Pervasives.app (cons 1 (cons 2 [])) (cons 3 []).

Definition y : Z := apply (fun n => Z.add n 1) 12.
