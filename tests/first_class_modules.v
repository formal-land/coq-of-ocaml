Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Record SET := {
  elt : Type;
  t : Type;
  empty : t;
  is_empty : t -> bool;
  mem : elt -> t -> bool;
  add : elt -> t -> t;
  singleton : elt -> t;
  remove : elt -> t -> t;
  union : t -> t -> t;
  inter : t -> t -> t;
  diff : t -> t -> t;
  compare : t -> t -> Z;
  equal : t -> t -> bool;
  subset : t -> t -> bool;
  iter : (elt -> unit) -> t -> unit;
  map : (elt -> elt) -> t -> t;
}.
