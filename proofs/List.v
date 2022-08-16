Require Import Libraries.
Require Import Basics.
Require Import Program.Program.
Require Import Coq.micromega.Lia.

Require Import Seq.
Local Open Scope Z_scope.
Import ListNotations.

Definition t (A : Set) : Set := list A.

Definition nil : forall {A : Set}, list A :=
  fun _ =>
  [].

Fixpoint length_aux {A : Set} (len : Z) (x : list A) : Z :=
  match x with
  | [] => len
  | cons a l => length_aux (Z.add len 1) l
  end.

Definition length {A : Set} (l : list A) : Z := length_aux 0 l.

Axiom length_cons : forall {A : Set} (x : A) (l : list A),
   length (x :: l) = length l + 1.

Lemma length_is_pos {A : Set} (l : list A) : 0 <= length l.
Proof.
  induction l.
  easy.
  rewrite IHl.
  rewrite length_cons.
  lia.
Qed.

Parameter compare_lengths : forall {a b : Set}, list a -> list b-> int.

Parameter compare_length_with : forall {a : Set}, list a -> int -> int.

(* Parameter cons : forall {a : Set}, a -> list a -> list a. *)

Definition hd : forall {a : Set}, list a -> option a :=
  fun _ l =>
    match l with
    | [] => None
    | x :: _ => Some x
    end.

Definition tl : forall {a : Set}, list a -> option (list a) :=
  fun _ l =>
    match l with
    | [] => None
    | _x :: m => Some m
    end.

Parameter nth : forall {A  : Set}, list A -> int -> A.

Parameter nth_opt : forall {A : Set}, list A -> int -> option A.

Definition rev {A : Set} (l : list A) : list A := rev_append l [].

Definition append {A : Set} : (list A) -> (list A) -> list A :=
  List.app (A := A).

Fixpoint rev_append {A : Set} (l1 : list A) (l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | cons a l => rev_append l (cons a l2)
  end.

Fixpoint flatten {A : Set} (x : list (list A)) : list A :=
  match x with
  | [] => []
  | cons l r => List.app l (flatten r)
  end.  

Definition concat {A : Set} : (list (list A)) -> list A := flatten.

(** Comparison **)
Fixpoint equal {a : Set} (eqb : a -> a -> bool) (l1 l2 : list a) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: l1, x2 :: l2 => eqb x1 x2 && equal eqb l1 l2
  | _, _ => false
  end.

Fixpoint compare {a : Set} (cmp : a -> a -> int) (l1 l2 : list a)
  : int :=
  match l1, l2 with
  | [], [] => 0
  | [], _ => -1
  | _, [] => 1
  | x :: l1, y :: l2 =>
    match cmp x y with
    | Z0 => compare cmp l1 l2
    | Zpos _ => 1
    | Zneg _ => -1
    end
  end.

(** Iterators **)
Definition iter : forall {a : Set},
  (a -> unit) -> list a -> unit :=
  fun a f l => tt.

Parameter iteri : forall {a : Set}, (int -> a -> unit) -> list a -> unit.

Fixpoint map {A B : Set} (f : A -> B) (x : list A) : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f a in
    cons r (map f l)
  end.

Fixpoint mapi_aux {A B : Set} (i : Z) (f : Z -> A -> B) (x : list A)
  : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f i a in
    cons r (mapi_aux (Z.add i 1) f l)
  end.

Definition mapi {A B : Set} (f : Z -> A -> B) (l : list A) : list B :=
  mapi_aux 0 f l.

Definition rev_map {A B : Set} (f : A -> B) (l : list A) : list B :=
  let fix rmap_f (accu : list B) (x : list A) : list B :=
    match x with
    | [] => accu
    | cons a l => rmap_f (cons (f a) accu) l
    end in
  rmap_f [] l.

Parameter filter_map : forall {a b : Set}, (a -> option b) -> list a -> list b.

Parameter concat_map : forall {a b : Set}, (a -> list b) -> list a -> list b.

Parameter fold_left_map : forall {a b c : Set}, (a -> b -> a * c) -> a -> list b -> a * list c.

Fixpoint fold_left {A B : Set} (f : A -> B -> A) (accu : A) (l : list B) : A :=
  match l with
  | [] => accu
  | cons a l => fold_left f (f accu a) l
  end.

Fixpoint fold_right {A B : Set} (f : A -> B -> B) (l : list A) (accu : B)
  : B :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
  end.

(** Iterators on two lists **)
Parameter iter2 : forall {a b : Set}, (a -> b -> unit) -> list a -> list b -> unit.

Parameter map2 : forall {a b c: Set}, (a -> b -> c) -> list a -> list b -> list c.

Parameter rev_map2 : forall {a b c: Set}, (a -> b -> c) -> list a -> list b -> list c.

Parameter fold_left2 : forall {a b c: Set}, (a -> b -> c -> a) -> a -> list b -> list c -> a.

Parameter fold_right2 : forall {a b c: Set}, (a -> b -> c -> c) -> list a -> list b -> c -> c.

(** List scanning **)
Fixpoint for_all {A : Set} (p : A -> bool) (x : list A) : bool :=
  match x with
  | [] => true
  | cons a l => andb (p a) (for_all p l)
  end.

Fixpoint _exists {A : Set} (p : A -> bool) (x : list A) : bool :=
  match x with
  | [] => false
  | cons a l => orb (p a) (_exists p l)
  end.

Parameter for_all2 : forall {a b : Set}, (a -> b -> bool) -> list a -> list b -> bool.

Parameter _exists2 : forall {a b : Set}, (a -> b -> bool) -> list a -> list b -> bool.

Fixpoint mem {A : Set} `{EqDec A} (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: l =>
    if equiv_decb x y then
      true
    else
      mem x l
  end.

Parameter memq : forall {a : Set}, a -> list a -> bool.

(** List searching **)
Parameter find : forall {a : Set}, (a -> bool) -> list a -> a.

Parameter find_opt : forall {a : Set}, (a -> bool) -> list a -> option a.

Parameter find_map : forall {a b: Set}, (a -> option b) -> list a -> option b.

Definition find_all {A : Set} (p : A -> bool) : (list A) -> list A :=
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

Definition filter {A : Set} : (A -> bool) -> (list A) -> list A := find_all.

Parameter filteri : forall {a : Set}, (int -> a -> bool) -> list a -> list a.

Definition partition {A : Set} (p : A -> bool) (l : list A)
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

(*
Parameter partition_map : 
  forall {a b c: Set}, (a -> Either.t (b, c)) -> list a -> list b * list c.
*)

(** Association lists **)
Parameter assoc : forall {a b : Set}, a -> list (a * b) -> b.

Parameter assoc_opt : forall {a b : Set}, a -> list (a * b) -> option b.

Parameter assq : forall {a b : Set}, a -> list (a * b) -> b.

Parameter assq_opt : forall {a b : Set}, a -> list (a * b) -> option b.

Fixpoint mem_assoc {A B : Set} `{EqDec A} (x : A) (l : list (A * B)) : bool :=
  match l with
  | [] => false
  | (y, v) :: l =>
    if equiv_decb x y then
      true
    else
      mem_assoc x l
  end.

Fixpoint remove_assoc {A B : Set} `{EqDec A} (x : A) (l : list (A * B))
  : list (A * B) :=
  match l with
  | [] => l
  | (y, v) :: l =>
    if equiv_decb x y then
      l
    else
      remove_assoc x l
  end.

Parameter remove_assq : forall {a b : Set}, a -> list (a * b) -> list (a * b).

(** Lists of pairs **)
Fixpoint split {A B : Set} (x : list (A * B)) : (list A) * (list B) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Parameter combine : forall {a b : Set}, list a -> list b -> list (a * b).

(** Sorting **)
Parameter sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter stable_sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter fast_sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter sort_uniq : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Fixpoint merge {A : Set} (cmp : A -> A -> Z) (l1 : list A) (l2 : list A)
  : list A :=
  let fix merge_aux (l2 : list A) : list A :=
    match (l1, l2) with
    | ([], l2) => l2
    | (l1, []) => l1
    | (cons h1 t1, cons h2 t2) =>
      if cmp h1 h2 <=? 0 then
        cons h1 (merge cmp t1 l2)
      else
        cons h2 (merge_aux t2)
    end in
  merge_aux l2.
Search seq.

(** Lists and Sequences **)
Parameter to_seq : forall {a : Set}, list a -> Seq.t a.

Parameter of_seq : forall {a : Set}, Seq.t a -> list a.
