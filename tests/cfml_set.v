Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Inductive set : Set :=
| Empty : set
| Node : set -> int -> set -> set.

Definition empty : set := Empty.

Fixpoint member (x : int) (s : set) : bool :=
  match s with
  | Empty => false
  | Node s1 y s2 =>
    if OCaml.Stdlib.lt x y then
      member x s1
    else
      if OCaml.Stdlib.lt y x then
        member x s2
      else
        true
  end.

Fixpoint insert (x : int) (s : set) : set :=
  match s with
  | Empty => Node Empty x Empty
  | Node s1 y s2 =>
    if OCaml.Stdlib.lt x y then
      Node (insert x s1) y s2
    else
      if OCaml.Stdlib.lt y x then
        Node s1 y (insert x s2)
      else
        s
  end.
