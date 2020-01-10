(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Parameter t : Set.

Parameter foo : t.

Parameter arg : forall (a b : Set), Set.

Parameter x : forall {a b : Set}, a -> b -> arg a b.

Module M.
  Inductive l (a : Set) : Set :=
  | Nil : l a
  | Cons : a -> l a -> l a.
  
  Arguments Nil {_}.
  Arguments Cons {_}.
  
  Parameter b : bool.
End M.