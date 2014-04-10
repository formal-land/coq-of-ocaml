Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition l1 : list Z := [].

Definition l2 : list Z := cons 1 (cons 2 (cons 3 (cons 4 []))).

Definition l3 : list (Z * string) :=
  cons (1, "one" % string) (cons (2, "two" % string) []).

Definition s1 : Z := OCaml.List.length l1.

Definition s2 : Z := OCaml.List.length l2.

Definition h {A : Type} (x : A) : M [ OCaml.Failure ] Z :=
  match x with
  | _ => OCaml.List.hd l2
  end.

Definition t {A : Type} (x : A) : M [ OCaml.Failure ] (list Z) :=
  match x with
  | _ => OCaml.List.tl l2
  end.

Definition x {A : Type} (x : A)
  : M [ OCaml.Failure; OCaml.Invalid_argument ] Z :=
  match x with
  | _ => OCaml.List.nth l2 1
  end.

Definition rl : list Z := List.rev l2.

Definition ll : list Z := OCaml.Pervasives.app l2 l2.

Definition rll : list Z := List.rev_append l2 l2.

Definition lc : list Z :=
  OCaml.List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition lf : list Z :=
  OCaml.List.flatten (cons l1 (cons l2 (cons l1 (cons l2 [])))).

Definition m : list Z := List.map (fun x => Z.add x 1) l2.

Definition mi : list Z := OCaml.List.mapi (fun i => fun x => Z.add x i) l2.

Definition rm : list Z := OCaml.List.rev_map (fun x => Z.add x 1) l2.

Definition fl : Z := OCaml.List.fold_left (fun s => fun x => Z.add s x) 0 l2.

Definition fr : Z := OCaml.List.fold_right (fun x => fun s => Z.add s x) l2 0.

Definition m2 {A : Type} (x_1 : A) : M [ OCaml.Invalid_argument ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition rm2 {A : Type} (x_1 : A) : M [ OCaml.Invalid_argument ] (list Z) :=
  match x_1 with
  | _ => OCaml.List.rev_map2 (fun x => fun y => Z.add x y) l2 l2
  end.

Definition fl2 {A : Type} (x_1 : A) : M [ OCaml.Invalid_argument ] Z :=
  match x_1 with
  | _ =>
    OCaml.List.fold_left2 (fun s => fun x => fun y => Z.add (Z.add s x) y) 0 l2
      l2
  end.

Definition fr2 {A : Type} (x_1 : A) : M [ OCaml.Invalid_argument ] Z :=
  match x_1 with
  | _ =>
    OCaml.List.fold_right2 (fun s => fun x => fun y => Z.add (Z.add s x) y) l2
      l2 0
  end.
