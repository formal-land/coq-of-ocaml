Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Fixpoint length_aux {A698 : Type} (len : Z) (x : list A698) : Z :=
  match x with
  | [] => len
  | cons a l => length_aux (Z.add len 1) l
  end.

Definition length {A730 : Type} (l : list A730) : Z := length_aux 0 l.

Definition hd {A739 : Type} (x : list A739) : M [ OCaml.Failure ] A739 :=
  match x with
  | [] => OCaml.Pervasives.failwith "hd" % string
  | cons a l => ret a
  end.

Definition tl {A772 : Type} (x : list A772) : M [ OCaml.Failure ] (list A772) :=
  match x with
  | [] => OCaml.Pervasives.failwith "tl" % string
  | cons a l => ret l
  end.

Definition nth {A791 : Type} (l : list A791) (n : Z) :
  M [ OCaml.Failure; OCaml.Invalid_argument ] A791 :=
  if OCaml.Pervasives.lt n 0 then
    lift [_;_] "01" (OCaml.Pervasives.invalid_arg "List.nth" % string)
  else
    lift [_;_] "10"
      (let fix nth_aux {A813 : Type} (l : list A813) (n : Z) :
        M [ OCaml.Failure ] A813 :=
        match l with
        | [] => OCaml.Pervasives.failwith "nth" % string
        | cons a l =>
          if equiv_decb n 0 then
            ret a
          else
            nth_aux l (Z.sub n 1)
        end in
      nth_aux l n).

Definition append {A886 : Type} : (list A886) -> (list A886) -> list A886 :=
  OCaml.Pervasives.app.

Fixpoint rev_append {A915 : Type} (l1 : list A915) (l2 : list A915) : list A915
  :=
  match l1 with
  | [] => l2
  | cons a l => rev_append l (cons a l2)
  end.

Definition rev {A932 : Type} (l : list A932) : list A932 := rev_append l [].

Fixpoint flatten {A961 : Type} (x : list (list A961)) : list A961 :=
  match x with
  | [] => []
  | cons l r => OCaml.Pervasives.app l (flatten r)
  end.

Definition concat {A976 : Type} : (list (list A976)) -> list A976 := flatten.

Fixpoint map {A1001 A998 : Type} (f : A1001 -> A998) (x : list A1001) :
  list A998 :=
  match x with
  | [] => []
  | cons a l =>
    let r := f a in
    cons r (map f l)
  end.

Fixpoint mapi_aux {A1041 A1047 : Type}
  (i : Z) (f : Z -> A1047 -> A1041) (x : list A1047) : list A1041 :=
  match x with
  | [] => []
  | cons a l =>
    let r := f i a in
    cons r (mapi_aux (Z.add i 1) f l)
  end.

Definition mapi {A1093 A1095 : Type} (f : Z -> A1095 -> A1093) (l : list A1095)
  : list A1093 := mapi_aux 0 f l.

Definition rev_map {A1142 A1145 : Type} (f : A1145 -> A1142) (l : list A1145) :
  list A1142 :=
  let fix rmap_f (accu : list A1142) (x : list A1145) : list A1142 :=
    match x with
    | [] => accu
    | cons a l => rmap_f (cons (f a) accu) l
    end in
  rmap_f [] l.

Fixpoint iter {A1188 A1190 : Type} (f : A1190 -> A1188) (x : list A1190) : unit
  :=
  match x with
  | [] => tt
  | cons a l => iter f l
  end.

Fixpoint iteri_aux {A1228 A1233 : Type}
  (i : Z) (f : Z -> A1233 -> A1228) (x : list A1233) : unit :=
  match x with
  | [] => tt
  | cons a l => iteri_aux (Z.add i 1) f l
  end.

Definition iteri {A1278 A1281 : Type} (f : Z -> A1278 -> A1281) (l : list A1278)
  : unit := iteri_aux 0 f l.

Fixpoint fold_left {A1323 A1326 : Type}
  (f : A1323 -> A1326 -> A1323) (accu : A1323) (l : list A1326) : A1323 :=
  match l with
  | [] => accu
  | cons a l => fold_left f (f accu a) l
  end.

Fixpoint fold_right {A1364 A1367 : Type}
  (f : A1364 -> A1367 -> A1367) (l : list A1364) (accu : A1367) : A1367 :=
  match l with
  | [] => accu
  | cons a l => f a (fold_right f l accu)
  end.

Fixpoint map2 {A1443 A1446 A1449 : Type}
  (f : A1446 -> A1449 -> A1443) (l1 : list A1446) (l2 : list A1449) :
  M [ OCaml.Invalid_argument ] (list A1443) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let r := f a1 a2 in
    let! x := map2 f l1 l2 in
    ret (cons r x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.map2" % string
  end.

Definition rev_map2 {A1556 A1559 A1562 : Type}
  (f : A1559 -> A1562 -> A1556) (l1 : list A1559) (l2 : list A1562) :
  M [ OCaml.Invalid_argument ] (list A1556) :=
  let fix rmap2_f (accu : list A1556) (l1 : list A1559) (l2 : list A1562) :
    M [ OCaml.Invalid_argument ] (list A1556) :=
    match (l1, l2) with
    | ([], []) => ret accu
    | (cons a1 l1, cons a2 l2) => rmap2_f (cons (f a1 a2) accu) l1 l2
    | (_, _) => OCaml.Pervasives.invalid_arg "List.rev_map2" % string
    end in
  rmap2_f [] l1 l2.

Fixpoint iter2 {A1660 A1662 A1665 : Type}
  (f : A1662 -> A1665 -> A1660) (l1 : list A1662) (l2 : list A1665) :
  M [ OCaml.Invalid_argument ] unit :=
  match (l1, l2) with
  | ([], []) => ret tt
  | (cons a1 l1, cons a2 l2) => iter2 f l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.iter2" % string
  end.

Fixpoint fold_left2 {A1759 A1762 A1765 : Type}
  (f : A1759 -> A1762 -> A1765 -> A1759) (accu : A1759) (l1 : list A1762)
  (l2 : list A1765) : M [ OCaml.Invalid_argument ] A1759 :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) => fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.fold_left2" % string
  end.

Fixpoint fold_right2 {A1850 A1853 A1856 : Type}
  (f : A1850 -> A1853 -> A1856 -> A1856) (l1 : list A1850) (l2 : list A1853)
  (accu : A1856) : M [ OCaml.Invalid_argument ] A1856 :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) =>
    let! x := fold_right2 f l1 l2 accu in
    ret (f a1 a2 x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.fold_right2" % string
  end.

Fixpoint for_all {A1912 : Type} (p : A1912 -> bool) (x : list A1912) : bool :=
  match x with
  | [] => true
  | cons a l => andb (p a) (for_all p l)
  end.

Fixpoint _exists {A1955 : Type} (p : A1955 -> bool) (x : list A1955) : bool :=
  match x with
  | [] => false
  | cons a l => orb (p a) (_exists p l)
  end.

Fixpoint for_all2 {A2038 A2041 : Type}
  (p : A2038 -> A2041 -> bool) (l1 : list A2038) (l2 : list A2041) :
  M [ OCaml.Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret true
  | (cons a1 l1, cons a2 l2) =>
    let! x := for_all2 p l1 l2 in
    ret (andb (p a1 a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.for_all2" % string
  end.

Fixpoint _exists2 {A2135 A2138 : Type}
  (p : A2135 -> A2138 -> bool) (l1 : list A2135) (l2 : list A2138) :
  M [ OCaml.Invalid_argument ] bool :=
  match (l1, l2) with
  | ([], []) => ret false
  | (cons a1 l1, cons a2 l2) =>
    let! x := _exists2 p l1 l2 in
    ret (orb (p a1 a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.exists2" % string
  end.

Fixpoint find {A2165 : Type} (p : A2165 -> bool) (x : list A2165) :
  M [ OCaml.Not_found ] A2165 :=
  match x with
  | [] => OCaml.raise_Not_found tt
  | cons x l =>
    if p x then
      ret x
    else
      find p l
  end.

Definition find_all {A2232 : Type} (p : A2232 -> bool) :
  (list A2232) -> list A2232 :=
  let fix find (accu : list A2232) (x : list A2232) : list A2232 :=
    match x with
    | [] => rev accu
    | cons x l =>
      if p x then
        find (cons x accu) l
      else
        find accu l
    end in
  find [].

Definition filter {A2276 : Type} : (A2276 -> bool) -> (list A2276) -> list A2276
  := find_all.

Definition partition {A2328 : Type} (p : A2328 -> bool) (l : list A2328) :
  (list A2328) * (list A2328) :=
  let fix part (yes : list A2328) (no : list A2328) (x : list A2328) :
    (list A2328) * (list A2328) :=
    match x with
    | [] => ((rev yes), (rev no))
    | cons x l =>
      if p x then
        part (cons x yes) no l
      else
        part yes (cons x no) l
    end in
  part [] [] l.

Fixpoint split {A2410 A2412 : Type} (x : list (A2410 * A2412)) :
  (list A2410) * (list A2412) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Fixpoint combine {A2493 A2494 : Type} (l1 : list A2493) (l2 : list A2494) :
  M [ OCaml.Invalid_argument ] (list (A2493 * A2494)) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let! x := combine l1 l2 in
    ret (cons (a1, a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.combine" % string
  end.

Fixpoint merge_rec {A2583 : Type}
  (counter : nat) (cmp : A2583 -> A2583 -> Z) (l1 : list A2583)
  (l2 : list A2583) : M [ NonTermination ] (list A2583) :=
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

Definition merge {A2583 : Type}
  (cmp : A2583 -> A2583 -> Z) (l1 : list A2583) (l2 : list A2583) :
  M [ Counter; NonTermination ] (list A2583) :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (merge_rec x cmp l1 l2).

Fixpoint chop {A2642 : Type} (k : Z) (l : list A2642) :
  M [ OCaml.Assert_failure ] (list A2642) :=
  if equiv_decb k 0 then
    ret l
  else
    match l with
    | cons x t => chop (Z.sub k 1) t
    | _ => OCaml.assert false
    end.
