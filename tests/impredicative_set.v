Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive t : Set :=
| Empty : t
| Node : forall {a : Set}, a -> t.

Fixpoint t_of_list {a : Set} (l : list a) : t :=
  match l with
  | [] => Empty
  | cons _ l =>
    let 'existT _ a l as exi := existT (A := Set) (fun a => list a) _ l
      return
        let fst := projT1 exi in
        let a := fst in
        t in
    Node (t_of_list l)
  end.
