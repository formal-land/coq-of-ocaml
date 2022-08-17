Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require CoqOfOCaml.Prelude.
Require CoqOfOCaml.Uchar.
Require CoqOfOCaml.Seq.
Require Import Ascii.

(* OCaml:
type t =
 {mutable buffer : bytes;
  mutable position : int;
  mutable length : int;
  initial_buffer : bytes}
  *)
Parameter t: Set.
Print string.
Parameter create : int -> t.
Parameter contents : t -> string.
Parameter to_bytes : t -> bytes.
Parameter sub : t -> int -> int -> string.
Parameter blit : t -> int -> bytes -> int -> int -> unit.
Parameter nth : t -> int -> ascii.
Parameter length : t -> int.
Parameter clear : t -> unit.
Parameter reset : t -> unit.
Parameter output_buffer : Prelude.out_channel -> t -> unit.
Parameter truncate : t -> int -> unit.
Parameter add_char : t -> ascii -> unit.
Parameter add_utf_8_uchar : t -> Uchar.t -> unit.
Parameter add_utf_16le_uchar : t -> Uchar.t -> unit.
Parameter add_utf_16be_uchar : t -> Uchar.t -> unit.
Parameter add_string : t -> string -> unit.
Parameter add_bytes : t -> bytes -> unit.
Parameter add_substring : t -> string -> int -> int -> unit.
Parameter add_subbytes : t -> bytes -> int -> int -> unit.
Parameter add_substitute : t -> (string -> string) -> string -> unit.
Parameter add_buffer : t -> t -> unit.
Parameter add_channel : t -> Prelude.in_channel -> int -> unit.
(** Buffers and Sequences **)
Parameter to_seq : t -> Seq.t char.
Parameter to_seqi : t -> Seq.t (int * char) .
Parameter add_seq : t -> Seq.t char -> unit.
Parameter of_seq : Seq.t char -> t.
(** Binary encoding of integers **)
Parameter add_uint8 : t -> int -> unit.
Parameter add_int8 : t -> int -> unit.
Parameter add_uint16_ne : t -> int -> unit.
Parameter add_uint16_be : t -> int -> unit.
Parameter add_uint16_le : t -> int -> unit.
Parameter add_int16_ne : t -> int -> unit.
Parameter add_int16_be : t -> int -> unit.
Parameter add_int16_le : t -> int -> unit.
Parameter add_int32_ne : t -> int32 -> unit.
Parameter add_int32_be : t -> int32 -> unit.
Parameter add_int32_le : t -> int32 -> unit.
Parameter add_int64_ne : t -> int64 -> unit.
Parameter add_int64_be : t -> int64 -> unit.
Parameter add_int64_le : t -> int64 -> unit.