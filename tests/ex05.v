Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition n : Z :=
  match ((cons 1 (cons 2 [])), false) with
  | (cons x (cons _ []), true) => x
  | (cons _ (cons y []), false) => y
  | _ => 0
  end.
