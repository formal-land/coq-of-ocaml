Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition Fail := Effect.make unit (string).
Extract Constant Fail => "Effect.Effect.Coq_make
exception Fail of Obj.t".

Definition raise_Fail {A : Type} (x : string) : M [ Fail ] A :=
  fun s => (inr (inl x), s).

Definition div (n : Z) : M [ Fail ] Z :=
  if equiv_decb n 0 then
    raise_Fail ("n is null" % string)
  else
    ret (Z.div 256 n).
