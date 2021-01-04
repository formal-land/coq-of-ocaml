Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Definition n : int :=
  match ([ 1; 2 ], false) with
  | (cons x (cons _ []), true) => x
  | (cons _ (cons y []), false) => y
  | _ => 0
  end.

Inductive t : Set :=
| Bar : int -> t
| Foo : bool -> string -> t.

Definition m (x : t) : int :=
  match
    (x,
      (let '_ := x in
      equiv_decb 1 2),
      match x with
      | Bar n => OCaml.Stdlib.gt n 12
      | _ => false
      end,
      match x with
      | Bar k => equiv_decb k 0
      | _ => false
      end) with
  | (_, true, _, _) => 3
  | (Bar n, _, true, _) => n
  | (Bar k, _, _, true) => k
  | (Bar n, _, _, _) => Z.opp n
  | (Foo _ _, _, _, _) => 0
  end.
