Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Definition option_value {a : Set} (x : option a) (default : a) : a :=
  match x with
  | Some x =>
    let 'existT _ a x as exi := existT (A := Set) (fun a => a) _ x
      return
        let fst := projT1 exi in
        let a := fst in
        a in
    x
  | None => default
  end.

Definition option_zero : option int -> int := fun x_1 => option_value x_1 0.

Definition option_value_bis {A : Set} : option A -> A -> A := option_value.
