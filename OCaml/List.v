Require Import Libraries.
Require Import Effect.
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

Definition hd {A : Type} (x : list A) : M [ Failure ] A :=
  match x with
  | [] => Pervasives.failwith "hd" % string
  | cons a l => ret a
  end.

Definition tl {A : Type} (x : list A) : M [ Failure ] (list A) :=
  match x with
  | [] => Pervasives.failwith "tl" % string
  | cons a l => ret l
  end.

Definition nth {A : Type} (l : list A) (n : Z)
  : M [ Failure; Invalid_argument ] A :=
  if Pervasives.lt n 0 then
    lift [_;_] "01" (Pervasives.invalid_arg "List.nth" % string)
  else
    lift [_;_] "10"
      (let fix nth_aux {B : Type} (l : list B) (n : Z)
        : M [ Failure ] B :=
        match l with
        | [] => Pervasives.failwith "nth" % string
        | cons a l =>
          if equiv_decb n 0 then
            ret a
          else
            nth_aux l (Z.sub n 1)
        end in
      nth_aux l n).

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

Fixpoint iter {A B : Type} (f : A -> B) (x : list A) : unit :=
  match x with
  | [] => tt
  | cons a l => iter f l
  end.

Fixpoint iteri_aux {A B : Type} (i : Z) (f : Z -> A -> B) (x : list A) : unit :=
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

Fixpoint fold_right {A B : Type} (f : A -> B -> B) (l : list A) (accu : B)
  : B :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
  end.

Fixpoint map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
  : M [ Invalid_argument ] (list C) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let r := f a1 a2 in
    let! x := map2 f l1 l2 in
    ret (cons r x)
  | (_, _) => Pervasives.invalid_arg "List.map2" % string
  end.

Definition rev_map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
  : M [ Invalid_argument ] (list C) :=
  let fix rmap2_f (accu : list C) (l1 : list A) (l2 : list B)
    : M [ Invalid_argument ] (list C) :=
    match (l1, l2) with
    | ([], []) => ret accu
    | (cons a1 l1, cons a2 l2) => rmap2_f (cons (f a1 a2) accu) l1 l2
    | (_, _) => Pervasives.invalid_arg "List.rev_map2" % string
    end in
  rmap2_f [] l1 l2.

Fixpoint iter2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
  : M [ Invalid_argument ] unit :=
  match (l1, l2) with
  | ([], []) => ret tt
  | (cons a1 l1, cons a2 l2) => iter2 f l1 l2
  | (_, _) => Pervasives.invalid_arg "List.iter2" % string
  end.

Fixpoint fold_left2 {A B C : Type}
  (f : A -> B -> C -> A) (accu : A) (l1 : list B) (l2 : list C)
  : M [ Invalid_argument ] A :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) => fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) => Pervasives.invalid_arg "List.fold_left2" % string
  end.

Fixpoint fold_right2 {A B C : Type}
  (f : A -> B -> C -> C) (l1 : list A) (l2 : list B) (accu : C)
  : M [ Invalid_argument ] C :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) =>
    let! x := fold_right2 f l1 l2 accu in
    ret (f a1 a2 x)
  | (_, _) => Pervasives.invalid_arg "List.fold_right2" % string
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
  : M [ Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret true
  | (cons a1 l1, cons a2 l2) =>
    let! x := for_all2 p l1 l2 in
    ret (andb (p a1 a2) x)
  | (_, _) => Pervasives.invalid_arg "List.for_all2" % string
  end.

Fixpoint _exists2 {A B : Type} (p : A -> B -> bool) (l1 : list A) (l2 : list B)
  : M [ Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret false
  | (cons a1 l1, cons a2 l2) =>
    let! x := _exists2 p l1 l2 in
    ret (orb (p a1 a2) x)
  | (_, _) => Pervasives.invalid_arg "List.exists2" % string
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

Fixpoint find {A : Type} (p : A -> bool) (x : list A)
  : M [ Not_found ] A :=
  match x with
  | [] => raise_Not_found tt
  | cons x l =>
    if p x then
      ret x
    else
      find p l
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

Fixpoint assoc {A B : Type} `{EqDec A} (x : A) (l : list (A * B))
  : M [ Not_found ] B :=
  match l with
  | [] => raise_Not_found ()
  | (y, v) :: l =>
    if equiv_decb x y then
      ret v
    else
      assoc x l
  end.

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

Fixpoint combine {A B : Type} (l1 : list A) (l2 : list B)
  : M [ Invalid_argument ] (list (A * B)) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let! x := combine l1 l2 in
    ret (cons (a1, a2) x)
  | (_, _) => Pervasives.invalid_arg "List.combine" % string
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

Fixpoint chop {A : Type} (k : Z) (l : list A) {struct l}
  : 0 <= k -> k <= length l -> { l' : list A | length l' = length l - k }.
  refine (
    match BinInt.Z.eq_dec k 0 with
    | left _ => fun Hk_pos Hk_le_length => exist _ l _
    | right Hk_neq_0 =>
      match l with
      | [] => fun Hk_pos Hk_le_length => !
      | cons x t => fun Hk_pos Hk_le_length =>
        let (l', _) := chop A (Z.sub k 1) t _ _ in
        exist _ l' _
      end
    end).
  - omega.
  - unfold length in Hk_le_length; simpl in Hk_le_length;
    omega.
  - omega.
  - rewrite length_cons in Hk_le_length; omega.
  - rewrite length_cons; omega.
Defined.

Module StableSort.
  Fixpoint rev_merge {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_aux (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        if Pervasives.le (cmp h1 h2) 0 then
          rev_merge cmp t1 l2 (cons h1 accu)
        else
          rev_merge_aux t2 (cons h2 accu)
      end in
    rev_merge_aux l2 accu.

  Fixpoint rev_merge_rev {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_rev_aux (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        if Pervasives.gt (cmp h1 h2) 0 then
          rev_merge_rev cmp t1 l2 (cons h1 accu)
        else
          rev_merge_rev_aux t2 (cons h2 accu)
      end in
    rev_merge_rev_aux l2 accu.

  Ltac sort_rec_tactic n n1 n2 Pl2 :=
    try (apply Z_div_pos; omega);
    try (
      assert (n = 2 * (n / 2) + (n mod 2)); [
        apply Z_div_mod_eq; omega|];
      assert (n2 = (n / 2) + (n mod 2)); [
        unfold n2, n1; omega|];
      assert (0 <= n1); [
       apply Z_div_pos; omega|];
      assert (0 <= n mod 2); [
        apply Z_mod_lt; omega|];
      omega);
    try (
      assert (n1 <= n); [
        unfold n1;
        assert (n / 2 = n - (n / 2) - (n mod 2)); [
          rewrite (Z_div_mod_eq n 2) at 2; omega|];
        assert (0 <= n / 2); [
          apply Z_div_pos; omega|];
        assert (0 <= n mod 2); [
          apply Z_mod_lt; omega|];
        omega|];
      omega);
    try (
      rewrite Pl2;
      assert (0 <= n / 2); [
        apply Z_div_pos; omega|];
      unfold n2, n1; omega).

  Fixpoint sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : 0 <= n -> n <= length l ->
      M [ NonTermination ] (list A)
  with rev_sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : 0 <= n -> n <= length l ->
      M [ NonTermination ] (list A).
  refine (
    match counter with
    | O => fun Hn_pos Hn_le_length => not_terminated tt
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) => fun Hn_pos Hn_le_length =>
        ret
          (if Pervasives.le (cmp x1 x2) 0 then
            cons x1 (cons x2 [])
          else
            cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) => fun Hn_pos Hn_le_length =>
        ret
          (if Pervasives.le (cmp x1 x2) 0 then
            if Pervasives.le (cmp x2 x3) 0 then
              cons x1 (cons x2 (cons x3 []))
            else
              if Pervasives.le (cmp x1 x3) 0 then
                cons x1 (cons x3 (cons x2 []))
              else
                cons x3 (cons x1 (cons x2 []))
          else
            if Pervasives.le (cmp x1 x3) 0 then
              cons x2 (cons x1 (cons x3 []))
            else
              if Pervasives.le (cmp x2 x3) 0 then
                cons x2 (cons x3 (cons x1 []))
              else
                cons x3 (cons x2 (cons x1 [])))
      | _ => fun Hn_pos Hn_le_length =>
        let n1 := n / 2 in
        let n2 := n - n1 in
        let (l2, Pl2) := chop n1 l _ _ in
        let! s1 := rev_sort_rec A counter cmp n1 l _ _ in
        let! s2 := rev_sort_rec A counter cmp n2 l2 _ _ in
        ret (rev_merge_rev cmp s1 s2 [])
      end
    end); sort_rec_tactic n n1 n2 Pl2.
  refine (
    match counter with
    | O => fun Hn_pos Hn_le_length => not_terminated tt
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) => fun Hn_pos Hn_le_length =>
        ret
          (if Pervasives.gt (cmp x1 x2) 0 then
            cons x1 (cons x2 [])
          else
            cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) => fun Hn_pos Hn_le_length =>
        ret
          (if Pervasives.gt (cmp x1 x2) 0 then
            if Pervasives.gt (cmp x2 x3) 0 then
              cons x1 (cons x2 (cons x3 []))
            else
              if Pervasives.gt (cmp x1 x3) 0 then
                cons x1 (cons x3 (cons x2 []))
              else
                cons x3 (cons x1 (cons x2 []))
          else
            if Pervasives.gt (cmp x1 x3) 0 then
              cons x2 (cons x1 (cons x3 []))
            else
              if Pervasives.gt (cmp x2 x3) 0 then
                cons x2 (cons x3 (cons x1 []))
              else
                cons x3 (cons x2 (cons x1 [])))
      | _ => fun Hn_pos Hn_le_length =>
        let n1 := n / 2 in
        let n2 := n - n1 in
        let (l2, Pl2) := chop n1 l _ _ in
        let! s1 := sort_rec A counter cmp n1 l _ _ in
        let! s2 := sort_rec A counter cmp n2 l2 _ _ in
        ret (rev_merge cmp s1 s2 [])
      end
    end); sort_rec_tactic n n1 n2 Pl2.
  Defined.

  Definition sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    (Hn_pos : 0 <= n) (Hn_le_length : n <= length l)
    : M [ Counter; NonTermination ] (list A) :=
    let! x := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (sort_rec x cmp n l Hn_pos Hn_le_length).

  Definition rev_sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    (Hn_pos : 0 <= n) (Hn_le_length : n <= length l)
    : M [ Counter; NonTermination ] (list A) :=
    let! x := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (rev_sort_rec x cmp n l Hn_pos Hn_le_length).
End StableSort.

Definition stable_sort {A : Type} (cmp : A -> A -> Z) (l : list A)
  : M [ Counter; NonTermination ] (list A).
  refine (
    let len := length l in
    if Pervasives.lt len 2 then
      ret l
    else
      StableSort.sort cmp len l _ _).
  - apply length_is_pos.
  - unfold len; omega.
Defined.

Definition sort {A : Type} : (A -> A -> Z) -> list A ->
  M [ Counter; NonTermination ] (list A) :=
  stable_sort.

Definition fast_sort {A : Type} : (A -> A -> Z) -> list A ->
  M [ Counter; NonTermination ] (list A) :=
  stable_sort.
