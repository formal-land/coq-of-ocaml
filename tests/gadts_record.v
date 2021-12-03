Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

(** Records for the constructor parameters *)
Module ConstructorRecords_term.
  Module term.
    Module T_Rec.
      Record record {x y : Set} : Set := Build {
        x : x;
        y : y }.
      Arguments record : clear implicits.
      Definition with_x {t_x t_y} x (r : record t_x t_y) :=
        Build t_x t_y x r.(y).
      Definition with_y {t_x t_y} y (r : record t_x t_y) :=
        Build t_x t_y r.(x) y.
    End T_Rec.
    Definition T_Rec_skeleton := T_Rec.record.
  End term.
End ConstructorRecords_term.
Import ConstructorRecords_term.

Reserved Notation "'term.T_Rec".

Inductive term : vtag -> Set :=
| T_Int : int -> term int_tag
| T_String : string -> term string_tag
| T_Pair : forall {a b : vtag}, term a -> term b -> term (tuple_tag a b)
| T_Rec : forall {a b : vtag},
  'term.T_Rec a (decode_vtag b) -> term (tuple_tag a b)

where "'term.T_Rec" :=
  (fun (t_a : vtag) (t_b : Set) => term.T_Rec_skeleton (term t_a) t_b).

Module term.
  Include ConstructorRecords_term.term.
  Definition T_Rec := 'term.T_Rec.
End term.

Fixpoint interp {a : vtag} (function_parameter : term a) : decode_vtag a :=
  match function_parameter with
  | T_Int n_value => n_value
  | T_String s_value => s_value
  | T_Pair p1 p2 => ((interp p1), (interp p2))
  | T_Rec {| term.T_Rec.x := x_value; term.T_Rec.y := y_value |} =>
    ((interp x_value), y_value)
  end.
