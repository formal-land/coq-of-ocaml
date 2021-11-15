Require Strings.Ascii.
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
Parameter op_tildeminuspoint : float -> float.

Parameter op_tildepluspoint : float -> float.

Parameter op_pluspoint : float -> float -> float.

Parameter op_minuspoint : float -> float -> float.

Parameter op_timespoint : float -> float -> float.

Parameter op_divpoint : float -> float -> float.

Parameter op_timestimespoint : float -> float -> float.

Parameter sqrt : float -> float.

Parameter exp : float -> float.

Parameter log : float -> float.

Parameter log10 : float -> float.

Parameter expm1 : float -> float.

Parameter log1p : float -> float.

Parameter cos : float -> float.

Parameter sin : float -> float.

Parameter tan : float -> float.

Parameter acos : float -> float.

Parameter asin : float -> float.

Parameter atan : float -> float.

Parameter atan2 : float -> float -> float.

Parameter hypot : float -> float -> float.

Parameter cosh : float -> float.

Parameter sinh : float -> float.

Parameter tanh : float -> float.

Parameter acosh : float -> float.

Parameter asinh : float -> float.

Parameter atanh : float -> float.

Parameter ceil : float -> float.

Parameter floor : float -> float.

Parameter abs_float : float -> float.

Parameter copysign : float -> float -> float.

Parameter mod_float : float -> float -> float.

Parameter frexp : float -> float * int.

Parameter ldexp : float -> int -> float.

Parameter modf : float -> float * float.

Parameter float_value : int -> float.

Parameter float_of_int : int -> float.

Parameter truncate : float -> int.

Parameter int_of_float : float -> int.

Parameter infinity : float.

Parameter neg_infinity : float.

Parameter nan : float.

Parameter max_float : float.

Parameter min_float : float.

Parameter epsilon_float : float.

Inductive fpclass : Set :=
| FP_normal
| FP_subnormal
| FP_zero
| FP_infinite
| FP_nan.

Parameter classify_float : float -> fpclass.

(** * String operations *)
Parameter op_caret : string -> string -> string.

(** * Character operations *)
Definition int_of_char (c : char) : int :=
  Z.of_nat (Ascii.nat_of_ascii c).

Parameter char_of_int : int -> char.

(** * Unit operations *)
Definition ignore {a : Set} (_ : a) : unit :=
  tt.

(** * String conversion functions *)
Definition string_of_bool (b : bool) : string :=
  if b then
    "true" % string
  else
    "false" % string.

Parameter bool_of_string_opt : string -> option bool.

Parameter bool_of_string : string -> bool.

Parameter string_of_int : int -> string.

Parameter int_of_string_opt : string -> option int.

Parameter int_of_string : string -> int.

Parameter string_of_float : float -> string.

Parameter float_of_string_opt : string -> option float.

Parameter float_of_string : string -> float.

(** * Pair operations *)
Definition fst : forall {a b : Set}, a * b -> a :=
  fun _ _ => fst.

Definition snd : forall {a b : Set}, a * b -> b :=
  fun _ _ => snd.

(** * List operations *)
Definition op_at : forall {a : Set}, list a -> list a -> list a :=
  List.app.

(** * Input/output *)
Parameter in_channel : Set.

Parameter out_channel : Set.

Parameter stdin : in_channel.

Parameter stdout : out_channel.

Parameter stderr : out_channel.

(** ** Output functions on standard output *)
Parameter print_char : char -> unit.

Parameter print_string : string -> unit.

Parameter print_bytes : bytes -> unit.

Parameter print_int : int -> unit.

Parameter print_float : float -> unit.

Parameter print_endline : string -> unit.

Parameter print_newline : unit -> unit.

(** ** Output functions on standard error *)
Parameter prerr_char : char -> unit.

Parameter prerr_string : string -> unit.

Parameter prerr_bytes : bytes -> unit.

Parameter prerr_int : int -> unit.

Parameter prerr_float : float -> unit.

Parameter prerr_endline : string -> unit.

Parameter prerr_newline : unit -> unit.

(** ** Input functions on standard input *)
Parameter read_line : unit -> string.

Parameter read_int_opt : unit -> option int.

Parameter read_int : unit -> int.

Parameter read_float_opt : unit -> option float.

Parameter read_float : unit -> float.

(** ** General output functions *)
Inductive open_flag : Set :=
| Open_rdonly
| Open_wronly
| Open_append
| Open_creat
| Open_trunc
| Open_excl
| Open_binary
| Open_text
| Open_nonblock.

Parameter open_out : string -> out_channel.

Parameter open_out_bin : string -> out_channel.

Parameter open_out_gen : list open_flag -> int -> string -> out_channel.

Parameter flush : out_channel -> unit.

Parameter flush_all : unit -> unit.

Parameter output_char : out_channel -> char -> unit.

Parameter output_string : out_channel -> string -> unit.

Parameter output_bytes : out_channel -> bytes -> unit.

Parameter output : out_channel -> bytes -> int -> int -> unit.

Parameter output_substring : out_channel -> string -> int -> int -> unit.

Parameter output_byte : out_channel -> int -> unit.

Parameter output_binary_int : out_channel -> int -> unit.

Parameter output_value : forall {a : Set}, out_channel -> a -> unit.

Parameter seek_out : out_channel -> int -> unit.

Parameter pos_out : out_channel -> int.

Parameter out_channel_length : out_channel -> int.

Parameter close_out : out_channel -> unit.

Parameter close_out_noerr : out_channel -> unit.

Parameter set_binary_mode_out : out_channel -> bool -> unit.

(** ** General input functions *)
Parameter open_in : string -> in_channel.

Parameter open_in_bin : string -> in_channel.

Parameter open_in_gen : list open_flag -> int -> string -> in_channel.

Parameter input_char : in_channel -> char.

Parameter input_line : in_channel -> string.

Parameter input : in_channel -> bytes -> int -> int -> int.

Parameter really_input : in_channel -> bytes -> int -> int -> unit.

Parameter really_input_string : in_channel -> int -> string.

Parameter input_byte : in_channel -> int.

Parameter input_binary_int : in_channel -> int.

Parameter input_value : forall {a : Set}, in_channel -> a.

Parameter seek_in : in_channel -> int -> unit.

Parameter pos_in : in_channel -> int.

Parameter in_channel_length : in_channel -> int.

Parameter close_in : in_channel -> unit.

Parameter close_in_noerr : in_channel -> unit.

Parameter set_binary_mode_in : in_channel -> bool -> unit.

(** ** Operations on large files *)
Module LargeFile.
  Parameter seek_out : out_channel -> int64 -> unit.

  Parameter pos_out : out_channel -> int64.

  Parameter out_channel_length : out_channel -> int64.

  Parameter seek_in : in_channel -> int64 -> unit.

  Parameter pos_in : in_channel -> int64.

  Parameter in_channel_length : in_channel -> int64.
End LargeFile.

(** * References *)
Record ref {a : Set} : Set := {
  contents : a;
}.
Arguments ref : clear implicits.

Parameter ref_value : forall {a : Set}, a -> ref a.

Parameter op_exclamation : forall {a : Set}, ref a -> a.

Parameter op_coloneq : forall {a : Set}, ref a -> a -> unit.

Parameter incr : ref int -> unit.

Parameter decr : ref int -> unit.

(** * Result type *)
Inductive result (a b : Set) : Set :=
| Ok : a -> result a b
| Error : b -> result a b.
Arguments Ok {_}.
Arguments Error {_}.

(** * Operations on format strings *)
Definition format6 : Set -> Set -> Set -> Set -> Set -> Set -> Set :=
  CamlinternalFormatBasics.format6.

Definition format4 (a b c d : Set) : Set := format6 a b c c c d.

Definition format (a b c : Set) : Set := format4 a b c c.

Parameter string_of_format : forall {a b c d e f : Set},
  format6 a b c d e f -> string.

Parameter format_of_string : forall {a b c d e f : Set},
  format6 a b c d e f -> format6 a b c d e f.

Parameter op_caretcaret : forall {a b c d e f g h : Set},
  format6 a b c d e f -> format6 f b c e g h -> format6 a b c d g h.

(** * Program termination *)
Parameter exit : forall {a : Set}, int -> a.

Parameter at_exit : (unit -> unit) -> unit.

(** * Standard library modules  *)
