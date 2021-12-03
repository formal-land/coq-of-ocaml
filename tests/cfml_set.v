Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive set : Set :=
| Empty : set
| Node : set -> int -> set -> set.

Definition empty : set := Empty.

Fixpoint member (x_value : int) (s_value : set) : bool :=
  match s_value with
  | Empty => false
  | Node s1 y_value s2 =>
    if CoqOfOCaml.Stdlib.lt x_value y_value then
      member x_value s1
    else
      if CoqOfOCaml.Stdlib.lt y_value x_value then
        member x_value s2
      else
        true
  end.

Fixpoint insert (x_value : int) (s_value : set) : set :=
  match s_value with
  | Empty => Node Empty x_value Empty
  | Node s1 y_value s2 =>
    if CoqOfOCaml.Stdlib.lt x_value y_value then
      Node (insert x_value s1) y_value s2
    else
      if CoqOfOCaml.Stdlib.lt y_value x_value then
        Node s1 y_value (insert x_value s2)
      else
        s_value
  end.
