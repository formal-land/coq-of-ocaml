Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

(** Init function; without side-effects in Coq *)
Definition init_module : unit :=
  let '_ := Z.add 1 1 in
  tt.

Module M.
  (** Init function; without side-effects in Coq *)
  Definition init_module : unit := OCaml.Stdlib.ignore (Z.add 1 1).
End M.
