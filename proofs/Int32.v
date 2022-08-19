Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Parameter zero : int32.
Parameter one : int32.
Parameter minus_one : int32.
Parameter neg : int32 -> int32.
Parameter add : int32 -> int32 -> int32.
Parameter sub : int32 -> int32 -> int32.
Parameter mul : int32 -> int32 -> int32.
Parameter div : int32 -> int32 -> int32.
Parameter unsigned_div : int32 -> int32 -> int32.
Parameter rem : int32 -> int32 -> int32.
Parameter unsigned_rem : int32 -> int32 -> int32.
Parameter succ : int32 -> int32.
Parameter pred : int32 -> int32.
Parameter abs : int32 -> int32.
Parameter max_int : int32.
Parameter min_int : int32.
Parameter logand : int32 -> int32 -> int32.
Parameter logor : int32 -> int32 -> int32.
Parameter logxor : int32 -> int32 -> int32.
Parameter lognot : int32 -> int32.
Parameter shift_left : int32 -> int -> int32.
Parameter shift_right : int32 -> int -> int32.
Parameter shift_right_logical : int32 -> int -> int32.
(** Type conversion **)
Parameter of_int : int -> int32.
Parameter to_int : int32 -> int.
Parameter unsigned_to_int : int32 -> option int.
Parameter of_float : float -> int32.
Parameter to_float : int32 -> float.
Parameter of_string : string -> int32.
Parameter of_string_opt : string -> option int32.
Parameter to_string : int32 -> string.
Parameter bits_of_float : float -> int32.
Parameter float_of_bits : int32 -> float.

Definition t := int32.
Parameter compare : t -> t -> int.
Parameter unsigned_compare : t -> t -> int.
Parameter equal : t -> t -> bool.
Parameter min : t -> t -> t.
Parameter max : t -> t -> t.
