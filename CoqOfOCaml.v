Require Export ZArith.
Require Export Ascii.
Require Export String.
Require Export List.
Require Export Program.Basics.
Require Export Classes.SetoidDec.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition int_of_char (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Definition char_of_int (n : Z) : ascii :=
  ascii_of_nat (Z.to_nat n).