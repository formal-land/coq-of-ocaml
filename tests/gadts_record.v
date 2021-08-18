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
  | T_Pair p1 p2 =>
    let 'existT _ [__1, __0] [p2, p1] as exi :=
      existT (A := [vtag ** vtag]) (fun '[__1, __0] => [term __1 ** term __0])
        [_, _] [p2, p1]
      return
        let fst := projT1 exi in
        let __0 := Primitive.snd fst in
        let __1 := Primitive.fst fst in
        decode_vtag __0 * decode_vtag __1 in
    ((interp p1), (interp p2))
  | T_Rec {| term.T_Rec.x := x; term.T_Rec.y := y |} =>
    let 'existT _ [__3, __2] [y, x] as exi :=
      existT (A := [Set ** vtag]) (fun '[__3, __2] => [__3 ** term __2]) [_, _]
        [y, x]
      return
        let fst := projT1 exi in
        let __2 := Primitive.snd fst in
        let __3 := Primitive.fst fst in
        decode_vtag __2 * __3 in
    ((interp x), y)
  end.
