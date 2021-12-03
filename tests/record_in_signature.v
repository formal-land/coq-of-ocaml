Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module Sig.
  Record signature {t : Set -> Set} : Set := {
    t := t;
    v_value : t string;
  }.
End Sig.
Definition Sig := @Sig.signature.
Arguments Sig {_}.

Module M.
  Module t.
    Record record {a : Set} : Set := Build {
      x : int;
      y : int;
      label : a }.
    Arguments record : clear implicits.
    Definition with_x {t_a} x (r : record t_a) :=
      Build t_a x r.(y) r.(label).
    Definition with_y {t_a} y (r : record t_a) :=
      Build t_a r.(x) y r.(label).
    Definition with_label {t_a} label (r : record t_a) :=
      Build t_a r.(x) r.(y) label.
  End t.
  Definition t := t.record.
  
  Definition v_value : t string := {| t.x := 0; t.y := 1; t.label := "hi" |}.
  
  Definition module :=
    {|
      Sig.v_value := v_value
    |}.
End M.
Definition M : Sig (t := _) := M.module.

Definition v_value : M.(Sig.t) string := M.(Sig.v_value).

Definition s_value : string := M.(Sig.v_value).(M.t.label).
