Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Reserved Notation "'t".

Inductive node (A : Set) : Set :=
| Nil : node A
| Cons : A -> 't A -> node A

where "'t" := (fun (T : Set) => unit -> node T).

Definition t := 't.

Arguments Nil {_}.
Arguments Cons {_}.
