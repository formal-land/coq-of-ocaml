Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Module Sig.
  Record signature {t : Set} : Set := {
    t := t;
    v : t;
  }.
End Sig.
Definition Sig := @Sig.signature.
Arguments Sig {_}.

Reserved Notation "'foo".

Inductive single : Set :=
| C : 'foo string -> single

where "'foo" := (fun (t_a : Set) => t_a * int * {_ : unit @ Sig (t := t_a)}).

Definition foo := 'foo.
