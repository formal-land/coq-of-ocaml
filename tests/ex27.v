Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint length_aux {A : Type} (len : Z) (x : list A) : Z :=
  match x with
  | [] => len
  | cons a l => length_aux (Z.add len 1) l
  end.

Definition length {A : Type} (l : list A) : Z := length_aux 0 l.

Definition hd {A : Type} (x : list A) : M [ OCaml.Failure ] A :=
  match x with
  | [] => OCaml.Pervasives.failwith "hd" % string
  | cons a l => ret a
  end.

Definition tl {A : Type} (x : list A) : M [ OCaml.Failure ] (list A) :=
  match x with
  | [] => OCaml.Pervasives.failwith "tl" % string
  | cons a l => ret l
  end.

Definition nth {A : Type} (l : list A) (n : Z) :
  M [ OCaml.Failure; OCaml.Invalid_argument ] A :=
  if OCaml.Pervasives.lt n 0 then
    lift [_;_] "01" (OCaml.Pervasives.invalid_arg "List.nth" % string)
  else
    lift [_;_] "10"
      (let fix nth_aux {A : Type} (l : list A) (n : Z) : M [ OCaml.Failure ] A
        :=
        match l with
        | [] => OCaml.Pervasives.failwith "nth" % string
        | cons a l =>
          if equiv_decb n 0 then
            ret a
          else
            nth_aux l (Z.sub n 1)
        end in
      nth_aux l n).

Definition append {A : Type} : (list A) -> (list A) -> list A :=
  OCaml.Pervasives.app.

Fixpoint rev_append {A : Type} (l1 : list A) (l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | cons a l => rev_append l (cons a l2)
  end.

Definition rev {A : Type} (l : list A) : list A := rev_append l [].

Fixpoint flatten {A : Type} (x : list (list A)) : list A :=
  match x with
  | [] => []
  | cons l r => OCaml.Pervasives.app l (flatten r)
  end.

Definition concat {A : Type} : (list (list A)) -> list A := flatten.

Fixpoint map {A B : Type} (f : A -> B) (x : list A) : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f a in
    cons r (map f l)
  end.

Fixpoint mapi_aux {A B : Type} (i : Z) (f : Z -> B -> A) (x : list B) : list A
  :=
  match x with
  | [] => []
  | cons a l =>
    let r := f i a in
    cons r (mapi_aux (Z.add i 1) f l)
  end.

Definition mapi {A B : Type} (f : Z -> B -> A) (l : list B) : list A :=
  mapi_aux 0 f l.

Fixpoint iter {A B : Type} (f : B -> A) (x : list B) : unit :=
  match x with
  | [] => tt
  | cons a l => iter f l
  end.

Fixpoint iteri_aux {A B : Type} (i : Z) (f : Z -> B -> A) (x : list B) : unit :=
  match x with
  | [] => tt
  | cons a l => iteri_aux (Z.add i 1) f l
  end.

Definition iteri {A B : Type} (f : Z -> A -> B) (l : list A) : unit :=
  iteri_aux 0 f l.

Fixpoint fold_left {A B : Type} (f : A -> B -> A) (accu : A) (l : list B) : A :=
  match l with
  | [] => accu
  | cons a l => fold_left f (f accu a) l
  end.

Fixpoint fold_right {A B : Type} (f : A -> B -> B) (l : list A) (accu : B) : B
  :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
  end.

Fixpoint map2 {A B C : Type} (f : B -> C -> A) (l1 : list B) (l2 : list C) :
  M [ OCaml.Invalid_argument ] (list A) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let r := f a1 a2 in
    let! x := map2 f l1 l2 in
    ret (cons r x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.map2" % string
  end.

Fixpoint iter2 {A B C : Type} (f : B -> C -> A) (l1 : list B) (l2 : list C) :
  M [ OCaml.Invalid_argument ] unit :=
  match (l1, l2) with
  | ([], []) => ret tt
  | (cons a1 l1, cons a2 l2) => iter2 f l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.iter2" % string
  end.

Fixpoint fold_left2 {A B C : Type}
  (f : A -> B -> C -> A) (accu : A) (l1 : list B) (l2 : list C) :
  M [ OCaml.Invalid_argument ] A :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) => fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.fold_left2" % string
  end.

Fixpoint fold_right2 {A B C : Type}
  (f : A -> B -> C -> C) (l1 : list A) (l2 : list B) (accu : C) :
  M [ OCaml.Invalid_argument ] C :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) =>
    let! x := fold_right2 f l1 l2 accu in
    ret (f a1 a2 x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.fold_right2" % string
  end.

Fixpoint for_all {A : Type} (p : A -> bool) (x : list A) : bool :=
  match x with
  | [] => true
  | cons a l => andb (p a) (for_all p l)
  end.

Fixpoint _exists {A : Type} (p : A -> bool) (x : list A) : bool :=
  match x with
  | [] => false
  | cons a l => orb (p a) (_exists p l)
  end.

Fixpoint for_all2 {A B : Type} (p : A -> B -> bool) (l1 : list A) (l2 : list B)
  : M [ OCaml.Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret true
  | (cons a1 l1, cons a2 l2) =>
    let! x := for_all2 p l1 l2 in
    ret (andb (p a1 a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.for_all2" % string
  end.

Fixpoint _exists2 {A B : Type} (p : A -> B -> bool) (l1 : list A) (l2 : list B)
  : M [ OCaml.Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret false
  | (cons a1 l1, cons a2 l2) =>
    let! x := _exists2 p l1 l2 in
    ret (orb (p a1 a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.exists2" % string
  end.

Fixpoint find {A : Type} (p : A -> bool) (x : list A) : M [ OCaml.Not_found ] A
  :=
  match x with
  | [] => OCaml.raise_Not_found tt
  | cons x l =>
    if p x then
      ret x
    else
      find p l
  end.

Fixpoint split {A B : Type} (x : list (A * B)) : (list A) * (list B) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Fixpoint combine {A B : Type} (l1 : list A) (l2 : list B) :
  M [ OCaml.Invalid_argument ] (list (A * B)) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let! x := combine l1 l2 in
    ret (cons (a1, a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.combine" % string
  end.

Fixpoint merge_rec {A : Type}
  (counter : nat) (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) :
  M [ NonTermination ] (list A) :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match (l1, l2) with
    | ([], l2) => ret l2
    | (l1, []) => ret l1
    | (cons h1 t1, cons h2 t2) =>
      if OCaml.Pervasives.le (cmp h1 h2) 0 then
        let! x := (merge_rec counter) cmp t1 l2 in
        ret (cons h1 x)
      else
        let! x := (merge_rec counter) cmp l1 t2 in
        ret (cons h2 x)
    end
  end.

Definition merge {A : Type} (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) :
  M [ Counter; NonTermination ] (list A) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (merge_rec x cmp l1 l2).

Fixpoint chop {A : Type} (k : Z) (l : list A) :
  M [ OCaml.Assert_failure ] (list A) :=
  if equiv_decb k 0 then
    ret l
  else
    match l with
    | cons x t => chop (Z.sub k 1) t
    | _ => OCaml.assert false
    end.
