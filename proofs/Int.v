Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Definition t := int.

Parameter zero : int.

Parameter one : int.

Parameter minus_one : int.

Parameter neg : int -> int.

Parameter add : int -> int -> int.

Parameter sub : int -> int -> int.

Parameter mul : int -> int -> int.

Parameter div : int -> int -> int.

Parameter rem : int -> int -> int.

Parameter succ : int -> int.

Parameter pred : int -> int.

Parameter abs : int -> int.

Parameter max_int : int.

Parameter min_int : int.

Parameter logand : int -> int -> int.

Parameter logor : int -> int -> int.

Parameter logxor : int -> int -> int.

Parameter lognot : int -> int.

Parameter shift_left : int -> int -> int.

Parameter shift_right : int -> int -> int.

Parameter shift_right_logical : int -> int -> int.

(** Predicates and comparisons **)
Parameter equal : int -> int -> bool.

Parameter compare : int -> int -> int.

Parameter min : int -> int -> int.

Parameter max : int -> int -> int.

(** Converting **)
Parameter to_float : int -> float.

Parameter of_float : float -> int.

Parameter to_string : int -> string.
