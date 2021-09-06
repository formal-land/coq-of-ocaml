Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive exp : vtag -> Set :=
| E_Int : int -> exp int_tag.

Module my_record.
  Record record {a : vtag} : Set := Build {
    x : exp a;
    y : int }.
  Arguments record : clear implicits.
  Definition with_x {t_a} x (r : record t_a) :=
    Build t_a x r.(y).
  Definition with_y {t_a} y (r : record t_a) :=
    Build t_a r.(x) y.
End my_record.
Definition my_record := my_record.record.

Definition get_x {a : vtag} (r : my_record a) : exp a :=
  let '{| my_record.x := x; my_record.y := y |} := r in
  x.
