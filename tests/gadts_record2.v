Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive exp : vtag -> Set :=
| E_Int : int -> exp int_tag.

(** Records for the constructor parameters *)
Module ConstructorRecords_term.
  Module term.
    Module T_constr.
      Record record {b : Set} : Set := Build {
        b : b }.
      Arguments record : clear implicits.
      Definition with_b {t_b} b (r : record t_b) :=
        Build t_b b.
    End T_constr.
    Definition T_constr_skeleton := T_constr.record.
  End term.
End ConstructorRecords_term.
Import ConstructorRecords_term.

Reserved Notation "'term.T_constr".

Inductive term : vtag -> Set :=
| T_constr : forall {a : vtag}, 'term.T_constr a -> term a

where "'term.T_constr" := (fun (t_a : vtag) => term.T_constr_skeleton (exp t_a)).

Module term.
  Include ConstructorRecords_term.term.
  Definition T_constr := 'term.T_constr.
End term.
