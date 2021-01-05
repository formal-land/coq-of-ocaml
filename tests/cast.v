Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition f (x : int) : int := Z.add (cast int x) 1.

Inductive t : Set :=
| Int : t.

Definition g {a : Set} (kind : t) (x : a) : int :=
  let 'Int := kind in
  Z.add (cast int x) 1.
