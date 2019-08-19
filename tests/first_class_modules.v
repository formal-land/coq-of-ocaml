Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Record SET := {
  elt : Type;
  t : Type;
  poly : forall {a : Type}, Type;
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
  for_all : (elt -> bool) -> t -> bool;
  _exists : (elt -> bool) -> t -> bool;
  filter : (elt -> bool) -> t -> t;
  partition : (elt -> bool) -> t -> t * t;
  cardinal : t -> Z;
  elements : t -> list elt;
  min_elt_opt : t -> option elt;
  max_elt_opt : t -> option elt;
  choose_opt : t -> option elt;
  split : elt -> t -> t * bool * t;
  find_opt : elt -> t -> option elt;
  find_first_opt : (elt -> bool) -> t -> option elt;
  find_last_opt : (elt -> bool) -> t -> option elt;
  of_list : (list elt) -> t;
}.
