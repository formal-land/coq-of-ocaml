Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Parameter zero : int64.
Parameter one : int64.
Parameter minus_one : int64.
Parameter neg : int64 -> int64.
Parameter add : int64 -> int64 -> int64.
Parameter sub : int64 -> int64 -> int64.
Parameter mul : int64 -> int64 -> int64.
Parameter div : int64 -> int64 -> int64.
Parameter unsigned_div : int64 -> int64 -> int64.
Parameter rem : int64 -> int64 -> int64.
Parameter unsigned_rem : int64 -> int64 -> int64.
Parameter succ : int64 -> int64.
Parameter pred : int64 -> int64.
Parameter abs : int64 -> int64.
Parameter max_int : int64.
Parameter min_int : int64.
Parameter logand : int64 -> int64 -> int64.
Parameter logor : int64 -> int64 -> int64.
Parameter logxor : int64 -> int64 -> int64.
Parameter lognot : int64 -> int64.
Parameter shift_left : int64 -> int -> int64.
Parameter shift_right : int64 -> int -> int64.
Parameter shift_right_logical : int64 -> int -> int64.
(** Conversion **)
Parameter of_int : int -> int64.
Parameter to_int : int64 -> int.
Parameter unsigned_to_int : int64 -> option int.
Parameter of_float : float -> int64.
Parameter to_float : int64 -> float.
Parameter of_int32 : int32 -> int64.
Parameter to_int32 : int64 -> int32.
Parameter of_nativeint : nativeint -> int64.
Parameter to_nativeint : int64 -> nativeint.
Parameter of_string : string -> int64.
Parameter of_string_opt : string -> option int64.
Parameter to_string : int64 -> string.
Parameter bits_of_float : float -> int64.
Parameter float_of_bits : int64 -> float.

Definition t := int64.
Parameter compare : t -> t -> int.
Parameter unsigned_compare : t -> t -> int.
Parameter equal : t -> t -> bool.
Parameter min : t -> t -> t.
Parameter max : t -> t -> t.
