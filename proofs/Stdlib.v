Require Import Strings.String.
Require Import ZArith.
Require Import CoqOfOCaml.Basics.

Local Open Scope Z_scope.

(** * Exceptions *)
Parameter raise : forall {a : Set}, exn -> a.

Parameter raise_notrace : forall {a : Set}, exn -> a.

Parameter invaliv_arg : forall {a : Set}, string -> a.

Parameter failwith : forall {a : Set}, string -> a.

Parameter Exit : exn.

Parameter Match_failure : string * int * int -> exn.

Parameter Assert_failure : string * int * int -> exn.

Parameter Invalid_argument : string -> exn.

Parameter Failure : string -> exn.

Parameter Not_found : exn.

Parameter Out_of_memory : exn.

Parameter Stack_overflow : exn.

Parameter Sys_error : string -> exn.

Parameter End_of_file : exn.

Parameter Division_by_zero : exn.

Parameter Sys_blocked_io : exn.

Parameter Undefined_recursive_module : string * int * int -> exn.

(** * Comparisons *)
Parameter op_eq : forall {a : Set}, a -> a -> bool.

Parameter op_ltgt : forall {a : Set}, a -> a -> bool.

Parameter op_lt : forall {a : Set}, a -> a -> bool.

Parameter op_gt : forall {a : Set}, a -> a -> bool.

Parameter op_lteq : forall {a : Set}, a -> a -> bool.

Parameter op_gteq : forall {a : Set}, a -> a -> bool.

Parameter compare : forall {a : Set}, a -> a -> int.

Parameter min : forall {a : Set}, a -> a -> a.

Parameter max : forall {a : Set}, a -> a -> a.

Parameter op_eqeq : forall {a : Set}, a -> a -> bool.

Parameter op_exclamationeq : forall {a : Set}, a -> a -> bool.

(** * Boolean operations *)
Definition not : bool -> bool := negb.

Definition op_andand : bool -> bool -> bool := andb.

Definition op_pipepipe : bool -> bool -> bool := orb.

(** * Debugging *)
Parameter __LOC__ : string.

Parameter __FILE__ : string.

Parameter __LINE__ : int.

Parameter __MODULE__ : string.

Parameter __POS__ : string * int * int * int.

Parameter __FUNCTION__ : string.

Parameter __LOC_OF__ : forall {a : Set}, a -> string * a.

Parameter __LINE_OF__ : forall {a : Set}, a -> int * a.

Parameter __POS_OF__ : forall {a : Set}, a -> (string * int * int * int) * a.

(** * Composition operators *)
(* `coq-of-ocaml` should unfold these operators to generate a cleaner output. *)

(** * Integer arithmetic *)
Parameter op_tildeminus : int -> int.

Parameter op_tildeplus : int -> int.

Definition succ (n : int) : int :=
  n + 1.

Definition pred (n : int) : int :=
  n - 1.

Definition op_plus : int -> int -> int := Z.add.

Definition op_minus : int -> int -> int := Z.sub.

Definition op_times : int -> int -> int := Z.mul.

Parameter op_div : int -> int -> int.

Definition _mod : int -> int -> int := Z.rem.

Definition abs : int -> int := Z.abs.

Definition max_int : int := 4611686018427387903.

Definition min_int : int := -4611686018427387904.

Parameter land : int -> int -> int.

Parameter lor : int -> int -> int.

Parameter lxor : int -> int -> int.

Parameter lnot : int -> int.

Parameter lsl : int -> int -> int.

Parameter lsr : int -> int -> int.

Parameter asr : int -> int -> int.

(** * Floating-point arithmetic *)


(** * String operations *)
(** * Character operations *)
(** * Unit operations *)
(** * String conversion functions *)
(** * Pair operations *)
(** * List operations *)
(** * Input/output *)
(** * References *)
(** * Result type *)
(** * Operations on format strings *)
(** * Program termination *)
(** * Standard library modules  *)
