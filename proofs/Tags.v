Require Import String.
Require Import Basics.

Inductive vtag : Type :=
| constr_tag : string -> Set -> vtag
| arrow_tag : vtag -> vtag -> vtag
| tuple_tag : vtag -> vtag -> vtag
(* | var_tag : forall (t0 : Type), vtag. *)
.

Fixpoint decode_vtag (tag : vtag) {struct tag}: Set :=
  match tag with
          | @constr_tag s t => t
          | arrow_tag t1 t2 => decode_vtag t1 -> decode_vtag t2
          | tuple_tag t1 t2 =>
            (decode_vtag t1) * (decode_vtag t2)
          (* | var_tag t => t *)
          end.

Notation int_tag := (constr_tag "int" int).
Notation string_tag := (constr_tag "string" string).
Notation bool_tag := (constr_tag "bool" bool).
Notation unit_tag := (constr_tag "unit" unit).
Notation float_tag := (constr_tag "float" int).
Notation option_tag A := (constr_tag "option" (option A)).
Notation list_tag A := (constr_tag "list" (list A)).
