Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Require CoqOfOCaml.Either.

Reserved Notation "'t".

Inductive node (A : Set) : Set :=
| Nil : node A
| Cons : A -> 't A -> node A

where "'t" := (fun (T : Set) => unit -> node T).

Definition t := 't.

Arguments Nil {_}.
Arguments Cons {_}.

(** Consuming sequences **)
Definition is_empty {a : Set} (xs : t a) : bool :=
  match xs tt with
  | Nil => true
  | Cons _ _ => false
  end.

Parameter uncons : forall {a : Set}, t a -> option (a * t a).

Fixpoint length_aux {a : Set} (accu : int) (n : node a) : int :=
  match n with
  | Nil => accu
  | Cons _ xs => length_aux (accu+1)%Z (xs tt)
  end.

Definition length {a : Set} (xs : t a) : int :=
  length_aux 0 (xs tt).

Fixpoint iter_node {a : Set} (f : a -> unit) (n : node a) : unit :=
  match n with
  | Nil => tt
  | Cons x s =>
    let _ := f x in
    iter_node f (s tt)
  end.

Definition iter {a : Set} (f : a -> unit) (seq : t a) : unit :=
  iter_node f (seq tt).

Fixpoint fold_left_node {a b : Set} (f : a -> b -> a) (acc : a) (n : node b) :
  a :=
  match n with
  | Nil => acc
  | Cons x s => fold_left_node f (f acc x) (s tt)
  end.

Definition fold_left {a b : Set} (f : a -> b -> a) (acc : a) (seq : t b) : a :=
  fold_left_node f acc (seq tt).

Fixpoint iteri_aux {a : Set} 
  (f : int -> a -> unit) (i : int) (n : node a) : unit :=
  match n with
  | Nil => tt
  | Cons x s =>
    let _ := f  i x in
    iteri_aux f (i+1)%Z (s tt)
  end.
  
Definition iteri{a : Set} (f : int -> a -> unit) (xs : t a) : unit :=
  iteri_aux f 0 (xs tt).

Fixpoint fold_lefti_aux {a b : Set} 
  (f : b -> int -> a -> b) (accu : b) (i : int) (n : node a) : b :=
  match n with
  | Nil => accu
  | Cons x xs => 
    let accu := f accu i x in
      fold_lefti_aux f accu (i+1)%Z (xs tt)
  end.

Definition fold_lefti {a b : Set} 
  (f : b -> int -> a -> b) (accu : b) (i : int) (xs : t a) : b :=
  fold_lefti_aux f accu 0 (xs tt).

Fixpoint for_all_node {a : Set} (p : a -> bool) (n : node a) : bool :=
  match n with
  | Nil => true
  | Cons x xs => p x && for_all_node p (xs tt)
  end.

Definition for_all {a : Set} (p : a -> bool) (xs : t a) : bool :=
  for_all_node p (xs tt).

Fixpoint _exists_node {a : Set} (p : a -> bool) (n : node a) : bool :=
  match n with
  | Nil => false
  | Cons x xs => p x || _exists_node p (xs tt)
  end.

Definition _exists {a : Set} (p : a -> bool) (xs : t a) : bool :=
  _exists_node p (xs tt).

Fixpoint find_node {a : Set} (p : a -> bool) (n : node a) : option a :=
  match n with
  | Nil => None
  | Cons x xs => if p x then Some x else find_node p (xs tt)
  end.

Definition find {a : Set} (p : a -> bool) (xs : t a) : option a :=
  find_node p (xs tt).

Fixpoint find_map_node {a b : Set} (f : a -> option b) (n : node a) : option b :=
  match n with
  | Nil => None
  | Cons x xs =>
    match f x with
    | None => find_map_node f (xs tt)
    | Some _ as result => result
    end
  end.

Definition find_map {a b : Set} (f : a -> option b) (xs : t a) : option b :=
  find_map_node f (xs tt).

Fixpoint iter2_node {a b : Set} (f : a -> b -> unit) (n : node a) (m : node b) :
  unit :=
  match n with
  | Nil => tt
  | Cons x xs =>
    match m with
    | Nil => tt
    | Cons y ys =>
      let _ := f x y in
      iter2_node f (xs tt) (ys tt)
    end
  end.

Definition iter2 {a b : Set} (f : a -> b -> unit) (xs : t a) (ys : t b) : unit :=
  iter2_node f (xs tt) (ys tt).

Fixpoint fold_left2_node {a b c : Set} 
  (f : a -> b -> c -> a) (accu : a) (n : node b) (m : node c) : a :=
  match n with
  | Nil => accu
  | Cons x xs =>
    match m with
    | Nil => accu
    | Cons y ys => let accu := f accu x y in
      fold_left2_node f accu (xs tt) (ys tt)
    end
  end.

Definition fold_left2 {a b c : Set} 
  (f : a -> b -> c -> a) (accu : a) (xs : t b) (ys : t c) : a :=
  fold_left2_node f accu (xs tt) (ys tt).

Fixpoint for_all2_node {a b : Set} 
  (f : a -> b -> bool) (n : node a) (m : node b) : bool :=
  match n with
  | Nil => true
  | Cons x xs =>
    match m with
    | Nil => true
    | Cons y ys => f x y && for_all2_node f (xs tt) (ys tt)
    end
  end.

Definition for_all2 {a b : Set} (f : a -> b -> bool) (xs : t a) (ys : t b) : bool :=
  for_all2_node f (xs tt) (ys tt).

Fixpoint _exists2_node {a b : Set} 
  (f : a -> b -> bool) (n : node a) (m : node b) : bool :=
  match n with
  | Nil => false
  | Cons x xs =>
    match m with
    | Nil => false
    | Cons y ys => f x y || _exists2_node f (xs tt) (ys tt)
    end
  end.

Definition _exists2 {a b : Set} (f : a -> b -> bool) (xs : t a) (ys : t b) : bool :=
  _exists2_node f (xs tt) (ys tt).

Fixpoint equal_node {a b: Set} 
  (eq : a -> b -> bool) (n : node a) (m : node b) : bool :=
  match n, m with
  | Nil, Nil => true
  | Cons x xs, Cons y ys => eq x y && equal_node eq (xs tt) (ys tt)
  | Nil, Cons _ _ => false
  | Cons _ _, Nil => false
  end.

Definition equal {a b : Set} (eq : a -> b -> bool) (xs : t a) (ys : t b) : bool :=
  equal_node eq (xs tt) (ys tt).

Fixpoint compare_node {a b : Set}
  (cmp : a -> b -> int) (n : node a) (m : node b) : int :=
  match n, m with
  | Nil, Nil => 0
  | Cons x xs, Cons y ys =>
    let c := cmp x y in
    if c =? 0 then compare_node cmp (xs tt) (ys tt) else c
  | Nil, Cons _ _ => -1
  | Cons _ _, Nil => 1
  end.

Definition compare {a b : Set} (cmp : a -> b -> int) (xs : t a) (ys : t b) : int :=
  compare_node cmp (xs tt) (ys tt).

(** Constructing sequences **)
Definition empty {a : Set} : t a :=
  fun _ => Nil.

Definition _return {a : Set} (x : a) : t a :=
  fun _ => Cons x empty.

Definition cons {a : Set} (x : a) (xs : t a) : t a :=
  fun _ => Cons x xs.

Parameter init : forall {a : Set},  int -> (int -> a) -> t a.

Parameter unfold : forall {a b : Set},  (b -> option (a * b)) -> b -> t a.

(* this is an infinite loop by design 
* "repeat x is the infinite sequence where"
* "the element x is repeated indefinitely."
* "repeat x is equivalent to cycle (return x)."*)
Parameter repeat : forall {a : Set},  a -> t a.

(*forever f is equivalent to map f (repeat ())*)
Parameter forever : forall {a : Set},  (unit -> a) -> t a.

(* cycle xs is the infinite sequence that consists 
* of an infinite number of repetitions of the sequence xs.*)
Parameter cycle : forall {a : Set},  t a -> t a.

(* iterate f x is the infinite sequence of values x, f x, f (f x), etc. *)
Parameter iterate : forall {a : Set},  (a -> a) -> a -> t a.

(** Transforming sequences **)
Fixpoint map_node {a b : Set} (f : a -> b) (n : node a) : node b :=
  match n with
  | Nil => Nil
  | Cons x xs => Cons (f x) (fun _ => map_node f (xs tt))
  end.

Definition map {a b : Set} (f : a -> b) (xs : t a) : t b :=
  fun _ => map_node f (xs tt).

Fixpoint mapi_aux {a b : Set} 
  (f : int -> a -> b) (i : int) (n : node a) : node b :=
  match n with
  | Nil => Nil
  | Cons x xs => Cons (f i x) (fun _ => mapi_aux f (i+1)%Z (xs tt))
  end.

Definition mapi {a b : Set} (f : int -> a -> b) (xs : t a) : t b :=
  fun _ => mapi_aux f 0 (xs tt).

Fixpoint filter_node {a : Set} (f : a -> bool) (n : node a) : node a :=
  match n with
  | Nil => Nil
  | Cons x xs =>
    if f x 
    then Cons x (fun _ => filter_node f (xs tt)) 
    else filter_node f (xs tt)
  end.

Definition filter {a : Set} (f : a -> bool) (xs : t a) : t a :=
  fun _ => filter_node f (xs tt).

Fixpoint filter_map_node {a b : Set} (f : a -> option b) (n : node a) : node b :=
  match n with
  | Nil => Nil
  | Cons x xs =>
    match f x with
    | None => filter_map_node f (xs tt)
    | Some y => Cons y (fun _ => filter_map_node f (xs tt))
    end
  end.

Definition filter_map {a b : Set} (f : a -> option b) (xs : t a) : t b :=
  fun _ => filter_map_node f (xs tt).

Fixpoint tail_scan_node {a b: Set} (f : b -> a -> b) (s : b) (n : node a) : node b :=
  match n with
  | Nil => Nil
  | Cons x xs => Cons (f s x) (fun _ => tail_scan_node f (f s x) (xs tt))
  end.

Definition scan {a b : Set} (f : b -> a -> b) (s : b) (xs : t a) : t b :=
  fun _ => tail_scan_node f s (xs tt).

Fixpoint take_aux {a : Set} (n : int) (xs : node a) : node a :=
  match xs with
  | Nil => Nil
  | Cons x xs =>
    if n =? 0
    then Nil
    else Cons x (fun _ => take_aux (n-1) (xs tt))
  end.

Definition take {a : Set} (n : int) (xs : t a) : t a :=
  if n <? 0
  then empty (* Invalid_argument "Seq.take"*)
  else fun _ => take_aux n (xs tt).

Fixpoint force_drop {a : Set} (n : int) (xs : node a) : node a :=
  match xs with
  | Nil => Nil
  | Cons _ xs =>
    let n := n-1 in
      if n =? 0
      then (xs tt)
      else force_drop (n-1) (xs tt)
  end.

Definition drop {a : Set} (n : int) (xs : t a) : t a :=
  if n <? 0
  then empty (* Invalid_argument "Seq.drop"*)
  else if n =? 0
    then xs
    else fun _ => force_drop n (xs tt).

Fixpoint take_while_node {a : Set} (f : a -> bool) (n : node a) : node a :=
  match n with
  | Nil => Nil
  | Cons x xs =>
    if f x
    then Cons x (fun _ => take_while_node f (xs tt))
    else Nil
  end.

Definition take_while {a : Set} (f : a -> bool) (xs : t a) : t a :=
  fun _ => take_while_node f (xs tt).

Fixpoint drop_while_node {a : Set} (f : a -> bool) (n : node a) : node a :=
  match n with
  | Nil => Nil
  | Cons x xs as node =>
    if f x
    then drop_while_node f (xs tt)
    else node
  end.

Definition drop_while {a : Set} (f : a -> bool) (xs : t a) : t a :=
  fun _ => drop_while_node f (xs tt).

Parameter group : forall {a : Set},  (a -> a -> bool) -> t a -> t (t a).

Parameter memoize : forall {a : Set},  t a -> t a.

(* exception Forced_twice. *)
(* This exception is raised when a sequence returned by Seq.once 
    (or a suffix of it) is queried more than once. *)

Parameter once : forall {a : Set},  t a -> t a.

Parameter transpose : forall {a : Set},  t (t a) -> t (t a).

(** Combining sequences **)
Fixpoint append_node {a : Set} (xs : node a) (ys : node a) : node a :=
  match xs with
  | Nil => ys
  | Cons x xs => Cons x (fun _ => append_node (xs tt) ys)
  end.

Definition append {a : Set} (xs : t a) (ys : t a) : t a :=
  fun _ => append_node (xs tt) (ys tt).

Fixpoint concat_node {a : Set} (xs : node (node a)) : node a :=
  match xs with
  | Nil => Nil
  | Cons x xs => append_node x (concat_node (xs tt))
  end.

Parameter concat : forall {a : Set},  t (t a) -> t a.

Parameter flat_map : forall {a b : Set},  (a -> t b) -> t a -> t b.

Parameter concat_map : forall {a b : Set},  (a -> t b) -> t a -> t b.

Parameter zip : forall {a b : Set},  t a -> t b -> t (a * b).

Parameter map2 : forall {a b c: Set},  (a -> b -> c) -> t a -> t b -> t c.

Parameter interleave : forall {a : Set},  t a -> t a -> t a.

Parameter sorted_merge : forall {a : Set},  (a -> a -> int) -> t a -> t a -> t a.

Parameter product : forall {a b : Set},  t a -> t b -> t (a * b).

Parameter map_product : forall {a b c : Set},  (a -> b -> c) -> t a -> t b -> t c.

(** Splitting a sequence into two sequences **)
Parameter unzip : forall {a b : Set},  t (a * b) -> t a * t b.

Parameter split : forall {a b : Set},  t (a * b) -> t a * t b.

Parameter partition_map : forall {a b c : Set},  
    (a -> Either.t b c) -> t a -> t b * t c.

Parameter partition : forall {a : Set},  (a -> bool) -> t a -> t a * t a.

(** Converting between sequences and dispensers **)
Parameter of_dispenser : forall {a : Set},  (unit -> option a) -> t a.

Parameter to_dispenser : forall {a : Set},  t a -> unit -> option a.

(** Sequences of integers **)
Parameter ints : forall {a : Set},  int -> t int.
