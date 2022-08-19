Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Parameter polymorphic_eq : forall {a : Set}, a -> a -> bool.

Parameter polymorphic_compare : forall {a : Set}, a -> a -> int.