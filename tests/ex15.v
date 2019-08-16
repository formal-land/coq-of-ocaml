Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive set : Type :=
| Empty : set
| Node : set -> Z -> set -> set.

Definition empty : set := Empty.

Fixpoint member (x : Z) (s : set) : bool :=
  match s with
  | Empty => false
  | Node s1 y s2 =>
    if OCaml.Pervasives.lt x y then
      member x s1
    else
      if OCaml.Pervasives.lt y x then
        member x s2
      else
        true
  end.

Fixpoint insert (x : Z) (s : set) : set :=
  match s with
  | Empty => Node Empty x Empty
  | Node s1 y s2 =>
    if OCaml.Pervasives.lt x y then
      Node (insert x s1) y s2
    else
      if OCaml.Pervasives.lt y x then
        Node s1 y (insert x s2)
      else
        s
  end.
