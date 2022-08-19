Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require CoqOfOCaml.Seq.
Require CoqOfOCaml.Uchar.

Definition t := string.

Fixpoint _make (n : nat) (c : ascii) : string :=
  match n with
  | O => EmptyString
  | S n => String c (_make n c)
  end.

(* TODO: raise an exception if n < 0. *)
Definition make (n : Z) (c : ascii) : string :=
  _make (Z.to_nat n) c.

Parameter init : int -> (int -> char) -> string.

Parameter empty : string.

Parameter of_bytes : bytes -> string.

Parameter to_bytes : string -> bytes.


Definition length (s : string) : Z :=
  Z.of_nat (String.length s).

(* TODO: raise an exception if n < 0. *)
Definition get (s : string) (n : Z) : ascii :=
  match String.get (Z.to_nat n) s with
  | None => "?" % char
  | Some c => c
  end.

(** Concatenating **)
Fixpoint concat (sep : string) (sl : list string) : string :=
  match sl with
  | [] => ""
  | [s] => s
  | s :: sl => String.append (String.append s sep) (concat sep sl)
  end.

Parameter cat : string -> string -> string.

Parameter equal : t -> t -> bool.

Parameter compare : t -> t -> int.

Parameter starts_with : string -> string -> bool.

Parameter ends_with : string -> string -> bool.

Parameter contains_from : string -> int -> char -> bool.

Parameter rcontains_from : string -> int -> char -> bool.

Parameter contains : string -> char -> bool.


(** Extracting substrings **)
(* TODO *)
Definition sub (s : string) (start : Z) (length : Z) : string :=
  s.

Parameter split_on_char : char -> string -> list string.

(** Transforming **)
Parameter map : (char -> char) -> string -> string.

Parameter mapi : (int -> char -> char) -> string -> string.

Parameter fold_left : forall {a : Set}, (a -> char -> a) -> a -> string -> a.

Parameter fold_right : forall {a : Set}, (char -> a -> a) -> string -> a -> a.

Parameter for_all : (char -> bool) -> string -> bool.

Parameter _exists : (char -> bool) -> string -> bool.

Parameter trim : string -> string.

(* TODO *)
Definition escaped (s : string) : string :=
  s.
Parameter uppercase_ascii : string -> string.

Parameter lowercase_ascii : string -> string.

Parameter capitalize_ascii : string -> string.

Parameter uncapitalize_ascii : string -> string.

(** Traversing **)
Parameter iter : (char -> unit) -> string -> unit.

Parameter iteri : (int -> char -> unit) -> string -> unit.

(** Searching **)
Parameter index_from : string -> int -> char -> int.

Parameter index_from_opt : string -> int -> char -> option int.

Parameter rindex_from : string -> int -> char -> int.

Parameter rindex_from_opt : string -> int -> char -> option int.

Parameter index : string -> char -> int.

Parameter index_opt : string -> char -> option int.

Parameter rindex : string -> char -> int.

Parameter rindex_opt : string -> char -> option int.

(** Strings and Sequences **)
Parameter to_seq : t -> Seq.t char.

Parameter to_seqi : t -> Seq.t (int * char).

Parameter of_seq : Seq.t char -> t.

(** UTF decoding and validations **)
Parameter get_utf_8_uchar : t -> int -> Uchar.utf_decode.

Parameter is_valid_utf_8 : t -> bool.

Parameter get_utf_16be_uchar : t -> int -> Uchar.utf_decode.

Parameter is_valid_utf_16be : t -> bool.

Parameter get_utf_16le_uchar : t -> int -> Uchar.utf_decode.

Parameter is_valid_utf_16le : t -> bool.

(** Deprecated functions **)
Parameter create : int -> bytes.

Parameter _set : bytes -> int -> char -> unit.

Parameter blit : string -> int -> bytes -> int -> int -> unit.

Parameter copy : string -> string.

Parameter fill : bytes -> int -> int -> char -> unit.

Parameter uppercase : string -> string.

Parameter lowercase : string -> string.

Parameter capitalize : string -> string.

Parameter uncapitalize : string -> string.

(** Binary decoding of integers **)
Parameter get_uint8 : string -> int -> int.

Parameter get_int8 : string -> int -> int.

Parameter get_uint16_ne : string -> int -> int.

Parameter get_uint16_be : string -> int -> int.

Parameter get_uint16_le : string -> int -> int.

Parameter get_int16_ne : string -> int -> int.

Parameter get_int16_be : string -> int -> int.

Parameter get_int16_le : string -> int -> int.

Parameter get_int32_ne : string -> int -> int32.

Parameter get_int32_be : string -> int -> int32.

Parameter get_int32_le : string -> int -> int32.

Parameter get_int64_ne : string -> int -> int64.

Parameter get_int64_be : string -> int -> int64.

Parameter get_int64_le : string -> int -> int64.
