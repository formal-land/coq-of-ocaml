Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition Err_Overflow := Effect.new unit unit.

Definition Err_Wtf := Effect.new unit (Z * string).
