Require Import OCaml.OCaml.

Set Primitive Projections.
Set Printing Projections.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope type_scope.
Import ListNotations.

Module T.
  Record signature {t : Set} : Set := {
    t := t;
    to_string : t -> string;
  }.
End T.

Module M.
  Definition t : Set := int.
  
  Definition to_string : int -> string := OCaml.Stdlib.string_of_int.
End M.

Definition int_to_string : int -> string := M.to_string.
