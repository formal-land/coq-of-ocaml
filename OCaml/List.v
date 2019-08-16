Require Import Libraries.
Require Import Basics.
Require Import Program.Program.

Local Open Scope Z_scope.
Import ListNotations.

Fixpoint length_aux {A : Type} (len : Z) (x : list A) : Z :=
  match x with
  | [] => len
  | cons a l => length_aux (Z.add len 1) l
  end.

Definition length {A : Type} (l : list A) : Z := length_aux 0 l.

Lemma length_cons {A : Type} (x : A) (l : list A)
  : length (x :: l) = length l + 1.
Admitted.

Lemma length_is_pos {A : Type} (l : list A) : 0 <= length l.
Admitted.

Definition append {A : Type} : (list A) -> (list A) -> list A :=
  Pervasives.app.

Fixpoint rev_append {A : Type} (l1 : list A) (l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | cons a l => rev_append l (cons a l2)
  end.

Definition rev {A : Type} (l : list A) : list A := rev_append l [].

Fixpoint flatten {A : Type} (x : list (list A)) : list A :=
  match x with
  | [] => []
  | cons l r => Pervasives.app l (flatten r)
  end.

Definition concat {A : Type} : (list (list A)) -> list A := flatten.

Fixpoint map {A B : Type} (f : A -> B) (x : list A) : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f a in
    cons r (map f l)
  end.

Fixpoint mapi_aux {A B : Type} (i : Z) (f : Z -> A -> B) (x : list A)
  : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f i a in
    cons r (mapi_aux (Z.add i 1) f l)
  end.

Definition mapi {A B : Type} (f : Z -> A -> B) (l : list A) : list B :=
  mapi_aux 0 f l.

Definition rev_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  let fix rmap_f (accu : list B) (x : list A) : list B :=
    match x with
    | [] => accu
    | cons a l => rmap_f (cons (f a) accu) l
    end in
  rmap_f [] l.

Fixpoint fold_left {A B : Type} (f : A -> B -> A) (accu : A) (l : list B) : A :=
  match l with
  | [] => accu
  | cons a l => fold_left f (f accu a) l
  end.

Fixpoint fold_right {A B : Type} (f : A -> B -> B) (l : list A) (accu : B)
  : B :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
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

Fixpoint mem {A : Type} `{EqDec A} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: l =>
    if equiv_decb x y then
      true
    else
      mem x l
  end.

Definition find_all {A : Type} (p : A -> bool) : (list A) -> list A :=
  let fix find (accu : list A) (x : list A) : list A :=
    match x with
    | [] => rev accu
    | cons x l =>
      if p x then
        find (cons x accu) l
      else
        find accu l
    end in
  find [].

Definition filter {A : Type} : (A -> bool) -> (list A) -> list A := find_all.

Definition partition {A : Type} (p : A -> bool) (l : list A)
  : (list A) * (list A) :=
  let fix part (yes : list A) (no : list A) (x : list A)
    : (list A) * (list A) :=
    match x with
    | [] => ((rev yes), (rev no))
    | cons x l =>
      if p x then
        part (cons x yes) no l
      else
        part yes (cons x no) l
    end in
  part [] [] l.

Fixpoint mem_assoc {A B : Type} `{EqDec A} (x : A) (l : list (A * B)) : bool :=
  match l with
  | [] => false
  | (y, v) :: l =>
    if equiv_decb x y then
      true
    else
      mem_assoc x l
  end.

Fixpoint remove_assoc {A B : Type} `{EqDec A} (x : A) (l : list (A * B))
  : list (A * B) :=
  match l with
  | [] => l
  | (y, v) :: l =>
    if equiv_decb x y then
      l
    else
      remove_assoc x l
  end.

Fixpoint split {A B : Type} (x : list (A * B)) : (list A) * (list B) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Fixpoint merge {A : Type} (cmp : A -> A -> Z) (l1 : list A) (l2 : list A)
  : list A :=
  let fix merge_aux (l2 : list A) : list A :=
    match (l1, l2) with
    | ([], l2) => l2
    | (l1, []) => l1
    | (cons h1 t1, cons h2 t2) =>
      if Pervasives.le (cmp h1 h2) 0 then
        cons h1 (merge cmp t1 l2)
      else
        cons h2 (merge_aux t2)
    end in
  merge_aux l2.
