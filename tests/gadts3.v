Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module Wrapper.
  Inductive tagged : Set :=
  | T1 : tagged
  | T2 : tagged
  | T3 : tagged.
End Wrapper.

Inductive term : vtag -> Set :=
| T_Int : int -> term int_tag
| T_String : string -> term string_tag
| T_Sum : term int_tag -> term int_tag -> term int_tag
| T_Wrap : Wrapper.tagged -> term (constr_tag "tagged" Wrapper.tagged).
