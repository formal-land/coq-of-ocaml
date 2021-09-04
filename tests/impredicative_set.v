Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive t : Set :=
| Empty : t
| Node : forall {a : Set}, a -> t.

Fixpoint t_of_list {a : Set} (l : list a) : t :=
  match l with
  | [] => Empty
  | cons _ l => Node (t_of_list l)
  end.
