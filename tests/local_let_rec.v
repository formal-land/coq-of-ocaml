Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Definition l {A : Type} (function_parameter : A) : list Z :=
  match function_parameter with
  | _ =>
    let fix map {B C : Type} (f : B -> C) (function_parameter : list B)
      : list C :=
      match function_parameter with
      | [] => []
      | cons x xs => cons (f x) (map f xs)
      end in
    let fix loop {B : Type} (x : B) : B :=
      x in
    map (fun n => Z.add n 1) (cons 5 (cons 7 (cons 8 [])))
  end.
