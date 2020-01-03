Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Parameter t : Type.

Parameter foo : t.

Parameter arg : forall (a b : Type), Type.

Parameter x : forall {a b : Type}, a -> b -> arg a b.

Module M.
  Inductive l (a : Type) : Type :=
  | Nil : l a
  | Cons : a -> l a -> l a.
  
  Arguments Nil {_}.
  Arguments Cons {_}.
  
  Parameter b : bool.
End M.
