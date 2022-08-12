Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require Import CoqOfOCaml.Prelude.

Parameter formatter : Set.

Parameter pp_print_list : forall {a : Set},
  option (formatter -> unit -> unit) -> (formatter -> a -> unit) ->
  formatter -> list a -> unit.

Parameter fprintf : forall {a : Set},
  formatter -> format a formatter unit -> a.

Parameter asprintf : forall {a : Set},
  format4 a formatter unit string -> a.
