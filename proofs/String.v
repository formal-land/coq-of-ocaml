Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

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
