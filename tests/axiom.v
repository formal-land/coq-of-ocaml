Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Axiom show : forall {a : Set}, a -> string.

Axiom recursive : forall {a : Set}, a -> string.
