(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Tezos.Environment.
Import Environment.Notations.
Require Tezos.Storage_description.

Parameter t : Set.

Definition raw_level : Set := t.

Parameter encoding : Data_encoding.t raw_level.

Parameter rpc_arg : RPC_arg.arg raw_level.

Parameter pp : Format.formatter -> raw_level -> unit.

Parameter Included_S : {_ : unit & Compare.S.signature (t := raw_level)}.

Definition op_eq : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_eq).

Definition op_ltgt : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_ltgt).

Definition op_lt : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_lt).

Definition op_lteq : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_lteq).

Definition op_gteq : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_gteq).

Definition op_gt : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.op_gt).

Definition compare : raw_level -> raw_level -> int :=
  (|Included_S|).(Compare.S.compare).

Definition equal : raw_level -> raw_level -> bool :=
  (|Included_S|).(Compare.S.equal).

Definition max : raw_level -> raw_level -> raw_level :=
  (|Included_S|).(Compare.S.max).

Definition min : raw_level -> raw_level -> raw_level :=
  (|Included_S|).(Compare.S.min).

Parameter to_int32 : raw_level -> int32.

Parameter of_int32_exn : int32 -> raw_level.

Parameter of_int32 : int32 -> Error_monad.tzresult raw_level.

Parameter diff : raw_level -> raw_level -> int32.

Parameter root : raw_level.

Parameter succ : raw_level -> raw_level.

Parameter pred : raw_level -> option raw_level.

Parameter Index :
  {_ : unit & Storage_description.INDEX.signature (t := raw_level)}.
