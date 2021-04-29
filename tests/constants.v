Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition c_int : int := 0.

Definition c_char : ascii := "c" % char.

Definition c_string : string := "c".

Definition c_float : float :=
  (* ❌ Float constant 1.0 is approximated by the integer 1 *)
  1.

Definition c_int32 : int32 :=
  (* ❌ Constant of type int32 is converted to int *)
  0.

Definition c_int64 : int64 :=
  (* ❌ Constant of type int64 is converted to int *)
  0.

Definition c_nativeint : nativeint :=
  (* ❌ Constant of type nativeint is converted to int *)
  0.
