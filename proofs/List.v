Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require Import Program.Program.
Require Import Coq.micromega.Lia.
Require Import CoqOfOCaml.Prelude.
Require CoqOfOCaml.Either.
Require CoqOfOCaml.Seq.
Local Open Scope Z_scope.
Import ListNotations.

Definition t (a : Set) : Set := list a.

Definition nil : forall {a : Set}, list a :=
  fun _ =>
  [].

Fixpoint length_aux {a : Set} (len : Z) (x : list a) : Z :=
  match x with
  | [] => len
  | cons a l => length_aux (Z.add len 1) l
  end.

Definition length {a : Set} (l : list a) : Z := length_aux 0 l.

Axiom length_cons : forall {a : Set} (x : a) (l : list a),
   length (x :: l) = length l + 1.

Lemma length_is_pos {a : Set} (l : list a) : 0 <= length l.
Proof.
  induction l.
  easy.
  rewrite IHl.
  rewrite length_cons.
  lia.
Qed.

Fixpoint compare_lengths {a b : Set} (l1 : list a) (l2 : list b) : int :=
  match l1, l2 with
  | [], [] => 0
  | [], _ => -1
  | _::li1, [] => 1
  | _::li1, _::li2 => (compare_lengths li1 li2)
  end.

Fixpoint compare_length_with {a : Set} (l1 : list a) (n : int) : int :=
  match l1 with
  | [] => if n =? 0 then 0 else 
            if n >? 0 then -1 else 1
  | _::tail => if n <=? 0 then 1 else compare_length_with tail (n-1)
  end.

(* Definition cons {a : Set} (a_value : a) (l: list a) := a_value::l. *)

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

Fixpoint nth_aux {a : Set} (l : list a) (n : int) : option a :=
  match l with 
  | [] => None
  | a :: l => if n =? 0 then Some a else nth_aux l (n-1)
  end.

(* require error handling https://github.com/ocaml/ocaml/blob/trunk/stdlib/list.ml#L41 *)
Axiom nth : forall {a  : Set}, list a -> int -> a.
(* require error handling https://github.com/ocaml/ocaml/blob/trunk/stdlib/list.ml#L46*)
Parameter nth_opt : forall {a : Set}, list a -> int -> option a.

Definition append {a : Set} : (list a) -> (list a) -> list a :=
  List.app (A := a).

Fixpoint rev_append {a : Set} (l1 : list a) (l2 : list a) : list a :=
  match l1 with
  | [] => l2
  | Lists.List.cons a l => rev_append l (cons a l2)
  end.

Definition rev {a : Set} (l : list a) : list a := rev_append l [].

Fixpoint flatten {a : Set} (x : list (list a)) : list a :=
  match x with
  | [] => []
  | cons l r => List.app l (flatten r)
  end.

Definition concat {a : Set} : (list (list a)) -> list a := flatten.

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
Fixpoint iter {a : Set} (f : a -> unit) (l : list a) : unit :=
  match l with
  | [] => ()
  | a::tail => let _ := f a in (iter f tail)
  end.

Fixpoint iteri {a : Set} (i : int) (f :int -> a -> unit) (l : list a) : unit :=
  match l with
  | [] => ()
  | a::tail => let _ := f i a in (iteri (i+1) f tail)
  end. 

Fixpoint map {a B : Set} (f : a -> B) (x : list a) : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f a in
    cons r (map f l)
  end.

Fixpoint mapi_aux {a B : Set} (i : Z) (f : Z -> a -> B) (x : list a)
  : list B :=
  match x with
  | [] => []
  | cons a l =>
    let r := f i a in
    cons r (mapi_aux (Z.add i 1) f l)
  end.

Definition mapi {a B : Set} (f : Z -> a -> B) (l : list a) : list B :=
  mapi_aux 0 f l.

Definition rev_map {a B : Set} (f : a -> B) (l : list a) : list B :=
  let fix rmap_f (accu : list B) (x : list a) : list B :=
    match x with
    | [] => accu
    | cons a l => rmap_f (cons (f a) accu) l
    end in
  rmap_f [] l.

Fixpoint filter_map {a b : Set} (f : a -> option b) (l : list a): list b :=
  match l with 
  | [] => []
  | x::xs =>
    match f x with
    | None => filter_map f xs
    | Some v => v :: filter_map f xs
    end
  end.

Definition concat_map {a b : Set} (f : a -> list b) (l: list a) : list b :=
  let fix concmap_f (accu : list b) (li : list a): list b :=
    match li with
    | [] => rev accu
    | x::l => 
      let xs := f x in 
        concmap_f (rev_append xs accu) l
    end in
  concmap_f [] l.

(*
Definition fold_left_map {a b c : Set} 
  (f : a -> b -> a * c) (a_value : a) (l : list b) : a * list c :=
  let fix fldleft_map (accu : a * list c) (l_accu : list b): a * list c :=
    match l with
    | [] => accu (rev l_accu)
    | x :: l =>
      let accu x := f accu x in
        fldleft_map (x::l_accu) l
    end in
  fldleft_map [] l.
  *)

Fixpoint fold_left {a B : Set} (f : a -> B -> a) (accu : a) (l : list B) : a :=
  match l with
  | [] => accu
  | cons a l => fold_left f (f accu a) l
  end.

Fixpoint fold_right {a B : Set} (f : a -> B -> B) (l : list a) (accu : B)
  : B :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
  end.

(** Iterators on two lists **)
Fixpoint iter2 {a b : Set} 
  (f : a -> b -> unit) (l1 : list a) (l2 : list b): unit :=
  match (l1, l2) with
  | ([], []) => ()
  | (a1::rest1, a2::rest2) => let _ := f a1 a2 in iter2 f rest1 rest2
  | (_,_) => ()
  (*| (_,_) => invalid_arg "List.iter2"*)
  end.

Fixpoint map2 {a b c: Set} 
  (f : a -> b -> c) (l1 : list a) (l2 : list b): list c :=
  match (l1, l2) with
  | ([], []) => []
  | ([a1], [b1]) => let r1 := f a1 b1 in [r1]
  | (a1::a2::l1, b1::b2::l2) => 
      let r1 := f a1 b1 in
      let r2 := f a2 b2 in
      r1::r2::map2 f l1 l2
  | (_, _) => []
(*| (_, _) -> invalid_arg "List.map2"*)
  end.

Definition rev_map2 {a b c: Set} 
  (f : a -> b -> c) (l1 : list a) (l2 : list b) :  list c :=
  let fix rmap2_f (accu : list c) (l1 : list a) (l2 : list b) :=
    match (l1, l2) with
    | ([], []) => accu
    | (a1::l1, a2::l2) => rmap2_f (f a1 a2 :: accu) l1 l2
    | (_, _) => []
    (*| (_, _) => Invalid_argument "List.rev_map2"*)
    end in
  rmap2_f [] l1 l2.

Fixpoint fold_left2 {a b c: Set} 
  (f : a -> b -> c -> a) (accu : a) (l1 : list b) (l2 : list c): a :=
  match (l1, l2) with
  | ([], []) => accu
  | (a1::l1, a2::l2) => fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) => accu
  (*| (_, _) => invalid_arg "List.fold_left2"*)
  end.

Fixpoint fold_right2 {a b c: Set} 
  (f : a -> b -> c -> c) (l1 : list a) (l2 : list b) (accu : c) : c :=
  match (l1, l2) with
  | ([], []) => accu
  | (a1::l1, a2::l2) => f a1 a2 (fold_right2 f l1 l2 accu)
  | (_, _) => accu
(*| (_, _) => invalid_arg "List.fold_right2"*)
  end.

(** List scanning **)
Fixpoint for_all {a : Set} (p : a -> bool) (x : list a) : bool :=
  match x with
  | [] => true
  | cons a l => andb (p a) (for_all p l)
  end.

Fixpoint _exists {a : Set} (p : a -> bool) (x : list a) : bool :=
  match x with
  | [] => false
  | cons a l => orb (p a) (_exists p l)
  end.

Fixpoint for_all2 {a b : Set} 
  (p: a -> b -> bool) (l1 : list a) (l2 : list b) : bool :=
  match (l1, l2) with
  | ([], []) => true
  | (a1::l1, a2::l2) => p a1 a2 && for_all2 p l1 l2
  | (_, _) => false
  (*| (_, _) => invalid_arg "List.for_all2"*)
  end.

Fixpoint _exists2 {a b : Set} 
  (p: a -> b -> bool) (l1 : list a) (l2 : list b) : bool :=
  match (l1, l2) with
  | ([], []) => false
  | (a1::l1, a2::l2) => (p a1 a2) || (_exists2 p l1 l2)
  | (_, _) => false
  (*| (_, _) -> invalid_arg "List.exists2"*)
  end.

Fixpoint mem {a : Set} `{EqDec a} (x : a) (l : list a) : bool :=
  match l with
  | [] => false
  | y :: l =>
    if equiv_decb x y then
      true
    else
      mem x l
  end.

Fixpoint memq {a : Set} `{EqDec a} (x : a) (l : list a) : bool :=
  match l with
  | [] => false
  | y::l => 
    if equiv_decb x y then
        true
      else
        memq x l
  end.

(** List searching **)
Fixpoint find {a : Set} (p : a -> bool) (l : list a) : a :=
  match l with
  | [] => raise Not_found
  | x :: l => if p x then x else find p l
  end.

Fixpoint find_opt {a : Set} (p : a -> bool) (l : list a): option a :=
  match l with
  | [] => None
  | x::l => if p x then Some x else find_opt p l
  end.

Fixpoint find_map {a b: Set} (f : a -> option b) (l : list a): option b :=
  match l with 
  | [] => None
  | x::l => 
    match f x with
    | Some _ as result => result
    | None => find_map f l
    end
  end.

Definition find_all {a : Set} (p : a -> bool) : (list a) -> list a :=
  let fix find (accu : list a) (x : list a) : list a :=
    match x with
    | [] => rev accu
    | cons x l =>
      if p x then
        find (cons x accu) l
      else
        find accu l
    end in
  find [].

Definition filter {a : Set} : (a -> bool) -> (list a) -> list a := find_all.

Definition filteri {a : Set} (p : int -> a -> bool) (l : list a) : list a :=
  let fix filteri_f (i : int) (l : list a):=
    match l with
    | [] => []
    | x::l =>
        let i := i + 1 in
        if p i x then x :: filteri_f i l else filteri_f i l
    end in
  filteri_f 0 l.

Definition partition {a : Set} (p : a -> bool) (l : list a)
  : (list a) * (list a) :=
  let fix part (yes : list a) (no : list a) (x : list a)
    : (list a) * (list a) :=
    match x with
    | [] => ((rev yes), (rev no))
    | cons x l =>
      if p x then
        part (cons x yes) no l
      else
        part yes (cons x no) l
    end in
  part [] [] l.

Fixpoint partition_map {a b c : Set}
(f : a -> Either.t b c) (l : list a)
: list b * list c :=
match l with
| [] => ([], [])
| x :: l' =>
  let '(l1, l2) := partition_map f l' in
  match f x with
  | Either.Left y => (y :: l1, l2)
  | Either.Right y => (l1, y :: l2)
  end
end.

(** Association lists **)
Fixpoint assoc {a b : Set} (x : a) (l : list (a * b)) : b :=
  match l with
  | [] => raise Not_found
  | (a,b)::l => 
    if compare x a = 0 then b else assoc x l
  end.

Parameter assoc_opt : forall {a b : Set}, a -> list (a * b) -> option b.

Parameter assq : forall {a b : Set}, a -> list (a * b) -> b.

Parameter assq_opt : forall {a b : Set}, a -> list (a * b) -> option b.

Fixpoint mem_assoc {a B : Set} `{EqDec a} (x : a) (l : list (a * B)) : bool :=
  match l with
  | [] => false
  | (y, v) :: l =>
    if equiv_decb x y then
      true
    else
      mem_assoc x l
  end.

Fixpoint remove_assoc {a B : Set} `{EqDec a} (x : a) (l : list (a * B))
  : list (a * B) :=
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
Fixpoint split {a B : Set} (x : list (a * B)) : (list a) * (list B) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Fixpoint combine {a b : Set} (l1 : list a) (l2 : list b) : list (a * b) :=
  match (l1, l2) with
    ([], []) => []
  | (a1::l1, a2::l2) => (a1, a2) :: combine l1 l2
  | (_, _) =>  []
  (*| (_, _) => invalid_arg "List.combine"*)
  end.

(** Sorting **)
Parameter sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter stable_sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter fast_sort : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Parameter sort_uniq : forall {a : Set}, (a -> a -> int) -> list a -> list a.

Fixpoint merge {a : Set} (cmp : a -> a -> Z) (l1 : list a) (l2 : list a)
  : list a :=
  let fix merge_aux (l2 : list a) : list a :=
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

(** Lists and Sequences **)
Fixpoint to_seq_node {a : Set} (l : list a) : Seq.node a :=
  match l with
  | [] => Seq.Nil
  | x :: l' => Seq.Cons x (fun _ => to_seq_node l')
  end.

Definition to_seq : forall {a : Set}, list a -> Seq.t a :=
  fun a l _ => to_seq_node l.

Fixpoint of_seq_node {a : Set} (s : Seq.node a) : list a :=
  match s with
  | Seq.Nil => []
  | Seq.Cons x f => x :: of_seq_node (f tt)
  end.
  
Definition of_seq : forall {a : Set}, Seq.t a -> list a :=
  fun a s => of_seq_node (s tt).
  
