Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require Import CoqOfOCaml.Prelude.
Require CoqOfOCaml.Buffer.
Require CoqOfOCaml.Either.

Parameter formatter : Set.

(** Pretty-printing boxes **)
Parameter pp_open_box : formatter -> int -> unit.

Parameter open_box : int -> unit.

Parameter pp_close_box : formatter -> unit -> unit.

Parameter close_box : unit -> unit.

Parameter pp_open_hbox : formatter -> unit -> unit.

Parameter open_hbox : unit -> unit.

Parameter pp_open_vbox : formatter -> int -> unit.

Parameter open_vbox : int -> unit.

Parameter pp_open_hvbox : formatter -> int -> unit.

Parameter open_hvbox : int -> unit.

Parameter pp_open_hovbox : formatter -> int -> unit.

Parameter open_hovbox : int -> unit.

(** Formatting functions **)
Parameter pp_print_string : formatter -> string -> unit.

Parameter print_string : string -> unit.

Parameter pp_print_bytes : formatter -> bytes -> unit.

Parameter print_bytes : bytes -> unit.

Parameter pp_print_as : formatter -> int -> string -> unit.

Parameter print_as : int -> string -> unit.

Parameter pp_print_int : formatter -> int -> unit.

Parameter print_int : int -> unit.

Parameter pp_print_float : formatter -> float -> unit.

Parameter print_float : float -> unit.

Parameter pp_print_char : formatter -> char -> unit.

Parameter print_char : char -> unit.

Parameter pp_print_bool : formatter -> bool -> unit.

Parameter print_bool : bool -> unit.

(** Break hints **)
Parameter pp_print_space : formatter -> unit -> unit.

Parameter print_space : unit -> unit.

Parameter pp_print_cut : formatter -> unit -> unit.

Parameter print_cut : unit -> unit.

Parameter pp_print_break : formatter -> int -> int -> unit.

Parameter print_break : int -> int -> unit.

Parameter pp_print_custom_break : formatter ->
  string * int * string -> string * int * string -> unit.

Parameter pp_force_newline : formatter -> unit -> unit.

Parameter force_newline : unit -> unit.

Parameter pp_print_if_newline : formatter -> unit -> unit.

Parameter print_if_newline : unit -> unit.

(** Pretty-printing termination **)
Parameter pp_print_flush : formatter -> unit -> unit.

Parameter print_flush : unit -> unit.

Parameter pp_print_newline : formatter -> unit -> unit.

Parameter print_newline : unit -> unit.

(** Margin **)
Parameter pp_set_margin : formatter -> int -> unit.

Parameter set_margin : int -> unit.

Parameter pp_get_margin : formatter -> unit -> int.

Parameter get_margin : unit -> int.

(** Maximum indentation limit **)
Parameter pp_set_max_indent : formatter -> int -> unit.

Parameter set_max_indent : int -> unit.

Parameter pp_get_max_indent : formatter -> unit -> int.

Parameter get_max_indent : unit -> int.

(** Geometry **)
Module geometry.
  Record record : Set := Build {
    max_indent : int;
    margin : int;
  }.
End geometry.

Parameter check_geometry : geometry.record -> bool.

Parameter pp_set_geometry : formatter -> int -> int -> unit.
(* the last two ints are geometry max_indent and margin *)
Parameter set_geometry : int -> int -> unit.

Parameter pp_safe_set_geometry : formatter -> int -> int -> unit.

Parameter safe_set_geometry : int -> int -> unit.

Parameter pp_update_geometry : formatter -> (geometry.record -> geometry.record) -> unit.

Parameter update_geometry : (geometry.record -> geometry.record) -> unit.

Parameter pp_get_geometry : formatter -> unit -> geometry.record.

Parameter get_geometry : unit -> geometry.record.

(** Maximum formatting depth **)
Parameter pp_set_max_boxes : formatter -> int -> unit.

Parameter set_max_boxes : int -> unit.

Parameter pp_get_max_boxes : formatter -> unit -> int.

Parameter pp_over_max_boxes : forall {b : Set}, formatter -> unit -> b.

Parameter over_max_boxes : unit -> bool.

(** Tabulation boxes **)
Parameter pp_open_tbox : formatter -> unit -> unit.

Parameter open_tbox : unit -> unit.

Parameter pp_close_tbox : formatter -> unit -> unit.

Parameter close_tbox : unit -> unit.

Parameter pp_set_tab : formatter -> unit -> unit.

Parameter set_tab : unit -> unit.

Parameter pp_print_tab : formatter -> unit -> unit.

Parameter print_tab : unit -> unit.

Parameter pp_print_tbreak : formatter -> int -> int -> unit.

Parameter print_tbreak : int -> int -> unit.

(** Ellipsis **)
Parameter pp_set_ellipsis_text : formatter -> string -> unit.

Parameter set_ellipsis_text : string -> unit.

Parameter pp_get_ellipsis_text : formatter -> unit -> string.

Parameter get_ellipsis_text : unit -> string.

(** Semantic tags **)
Definition tag := string.
Definition stag := tag. (*Obj.String_tag in OCaml*)
Parameter pp_open_stag : formatter -> stag -> unit.

Parameter open_stag : stag -> unit.

Parameter pp_close_stag : formatter -> unit -> unit.

Parameter close_stag : unit -> unit.

Parameter pp_set_tags : formatter -> bool -> unit.

Parameter set_tags : bool -> unit.

Parameter pp_set_print_tags : formatter -> bool -> unit.

Parameter set_print_tags : bool -> unit.

Parameter pp_set_mark_tags : formatter -> bool -> unit.

Parameter set_mark_tags : bool -> unit.

Parameter pp_get_print_tags : formatter -> unit -> bool.

Parameter get_print_tags : unit -> bool.

Parameter pp_get_mark_tags : formatter -> unit -> bool.

Parameter get_mark_tags : unit -> bool.

Parameter pp_set_formatter_out_channel : formatter -> out_channel -> unit.

(** Redirecting the standard formatter output **)
Parameter set_formatter_out_channel : out_channel -> unit.

Parameter pp_set_formatter_output_functions : formatter -> (string -> int -> int -> unit) -> (unit -> unit) -> unit.

Parameter set_formatter_output_functions : (string -> int -> int -> unit) -> (unit -> unit) -> unit.

Parameter pp_get_formatter_output_functions : formatter -> unit -> (string -> int -> int -> unit) * (unit -> unit).

Parameter get_formatter_output_functions : unit -> (string -> int -> int -> unit) * (unit -> unit).

(** Redefining formatter output **)
Module formatter_out_functions.
  Record record : Set := Build {
    out_string : string -> int -> int -> unit;
    out_flush : unit -> unit;
    out_newline : unit -> unit;
    out_spaces : int -> unit;
    out_indent : int -> unit;
  }.
End formatter_out_functions.
Parameter pp_set_formatter_out_functions : formatter -> formatter_out_functions.record -> unit.

Parameter set_formatter_out_functions : formatter_out_functions.record -> unit.

Parameter pp_get_formatter_out_functions : formatter -> unit -> formatter_out_functions.record.

Parameter get_formatter_out_functions : unit -> formatter_out_functions.record.

(** Redefining semantic tag operations **)
Module formatter_stag_functions.
  Record record : Set := Build {
    mark_open_stag : stag -> string;
    mark_close_stag : stag -> string;
    print_open_stag : stag -> unit;
    print_close_stag : stag -> unit;
  }.
End formatter_stag_functions.

Parameter pp_set_formatter_stag_functions : formatter -> formatter_stag_functions.record -> unit.

Parameter set_formatter_stag_functions : formatter_stag_functions.record -> unit.

Parameter pp_get_formatter_stag_functions : formatter -> unit -> formatter_stag_functions.record.

Parameter get_formatter_stag_functions : unit -> formatter_stag_functions.record.

(** Defining formatters**)
Parameter formatter_of_out_channel : out_channel -> formatter.

Parameter std_formatter : formatter.

Parameter err_formatter : formatter.

Parameter formatter_of_buffer : Buffer.t -> formatter.

Parameter stdbuf : Buffer.t.

Parameter str_formatter : formatter.

Parameter flush_str_formatter : unit -> string.

Parameter make_formatter : (string -> int -> int -> unit) -> (unit -> unit) -> formatter.

Parameter formatter_of_out_functions : formatter_out_functions.record -> formatter.

(** Symbolic pretty-printing **)
Inductive symbolic_output_item :=
| Output_flush
| Output_newline
| Output_string
| Output_spaces
| Output_indent.

Parameter symbolic_output_buffer : Set.

Parameter make_symbolic_output_buffer : unit -> symbolic_output_buffer.

Parameter clear_symbolic_output_buffer : symbolic_output_buffer -> unit.

Parameter get_symbolic_output_buffer : symbolic_output_buffer -> list symbolic_output_item.

Parameter flush_symbolic_output_buffer : symbolic_output_buffer -> list symbolic_output_item.

Parameter add_symbolic_output_item : symbolic_output_buffer -> symbolic_output_item -> unit.

Parameter formatter_of_symbolic_output_buffer : symbolic_output_buffer -> formatter.

(** Convenience formatting functions **)
Parameter pp_print_list : forall {a : Set},
  option (formatter -> unit -> unit) -> (formatter -> a -> unit) -> formatter -> list a -> unit.

Parameter pp_print_seq : forall {a : Set},
 (formatter -> unit -> unit) -> (formatter -> a -> unit) -> formatter -> Seq.t a -> unit.

Parameter pp_print_text : formatter -> string -> unit.

Parameter pp_print_option : forall {a : Set},
  (formatter -> unit -> unit) -> (formatter -> a -> unit) -> formatter -> option a -> unit.

Parameter pp_print_result : forall {a e: Set}, (formatter -> a -> unit) ->
  (formatter -> e -> unit) ->
  formatter -> result a e -> unit.

Parameter pp_print_either : forall {a b: Set},
  (formatter -> a -> unit) ->
  (formatter -> b -> unit) ->
  formatter -> Either.t a b  -> unit.

(** Formatted pretty-printing **)
Parameter fprintf : forall {a : Set},
  formatter -> format a formatter unit -> a.

Parameter printf : forall {a : Set}, format a formatter unit -> a.

Parameter eprintf : forall {a : Set}, format a formatter unit -> a.

Parameter sprintf : forall {a : Set}, format a unit string -> a.

Parameter asprintf : forall {a : Set},
  format4 a formatter unit string -> a.

Parameter dprintf : forall {a : Set}, format4 a formatter unit (formatter -> unit) -> a.

Parameter ifprintf : forall {a : Set}, formatter -> format a formatter unit -> a.

Parameter kfprintf : forall {a b : Set}, (formatter -> a) ->
  formatter -> format4 b formatter unit a -> b.

Parameter kdprintf : forall {a b : Set}, (formatter -> unit) -> a ->
  format4 b formatter unit a  -> b.

Parameter ikfprintf : forall {a b : Set}, (formatter -> a) ->
formatter -> format4 b formatter unit a -> b.

Parameter ksprintf : forall {a b : Set}, (string -> a) -> format4 b unit string a -> b.

Parameter kasprintf : forall {a b : Set}, (string -> a) -> format4 b formatter unit a -> b.

(** Deprecated **)
Parameter bprintf : forall {a : Set}, Buffer.t -> format a formatter unit -> a.

Parameter kprintf : forall {a b : Set}, (string -> a) -> format4 b unit string a  -> b.

Parameter set_all_formatter_output_functions : (string -> int -> int -> unit) -> (unit -> unit) -> (unit -> unit) -> (int -> unit) -> unit.

Parameter pp_get_all_formatter_output_functions : formatter -> unit -> (string -> int -> int -> unit) * (unit -> unit) * (unit -> unit) * (int -> unit).

(** Deprecated String tags**)
Parameter pp_open_tag : formatter -> tag -> unit.

Parameter open_tag : tag -> unit.

Parameter pp_close_tag : formatter -> unit -> unit.

Parameter close_tag : unit -> unit.

Module formatter_tag_functions.
  Record record : Set := Build {
    mark_open_tag : tag -> string;
    mark_close_tag : tag -> string;
    print_open_tag : tag -> unit;
    print_close_tag : tag -> unit;
  }.
End formatter_tag_functions.

Parameter pp_set_formatter_tag_functions : formatter -> formatter_stag_functions.record -> unit.

Parameter set_formatter_tag_functions : formatter_stag_functions.record -> unit.

Parameter pp_get_formatter_tag_functions : formatter -> unit -> formatter_stag_functions.record.

Parameter get_formatter_tag_functions : unit -> formatter_stag_functions.record.
