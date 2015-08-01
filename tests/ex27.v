Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

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

Definition nth {A : Type} (l : list A) (n : Z)
  : M [ OCaml.Failure; OCaml.Invalid_argument ] A :=
  if OCaml.Pervasives.lt n 0 then
    lift [_;_] "01" (OCaml.Pervasives.invalid_arg "List.nth" % string)
  else
    lift [_;_] "10"
      (let fix nth_aux_coq_rec {B : Type} (l : list B) (n : Z)
        : M [ OCaml.Failure ] B :=
        match l with
        | [] => OCaml.Pervasives.failwith "nth" % string
        | cons a l =>
          if equiv_decb n 0 then
            ret a
          else
            nth_aux_coq_rec l (Z.sub n 1)
        end in
      nth_aux_coq_rec l n).

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
  let fix rmap_f_coq_rec (accu : list B) (x : list A) : list B :=
    match x with
    | [] => accu
    | cons a l => rmap_f_coq_rec (cons (f a) accu) l
    end in
  rmap_f_coq_rec [] l.

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
  : M [ OCaml.Invalid_argument ] (list C) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let r := f a1 a2 in
    let! x := map2 f l1 l2 in
    ret (cons r x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.map2" % string
  end.

Definition rev_map2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
  : M [ OCaml.Invalid_argument ] (list C) :=
  let fix rmap2_f_coq_rec (accu : list C) (l1 : list A) (l2 : list B)
    : M [ OCaml.Invalid_argument ] (list C) :=
    match (l1, l2) with
    | ([], []) => ret accu
    | (cons a1 l1, cons a2 l2) => rmap2_f_coq_rec (cons (f a1 a2) accu) l1 l2
    | (_, _) => OCaml.Pervasives.invalid_arg "List.rev_map2" % string
    end in
  rmap2_f_coq_rec [] l1 l2.

Fixpoint iter2 {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B)
  : M [ OCaml.Invalid_argument ] unit :=
  match (l1, l2) with
  | ([], []) => ret tt
  | (cons a1 l1, cons a2 l2) => iter2 f l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.iter2" % string
  end.

Fixpoint fold_left2 {A B C : Type}
  (f : A -> B -> C -> A) (accu : A) (l1 : list B) (l2 : list C)
  : M [ OCaml.Invalid_argument ] A :=
  match (l1, l2) with
  | ([], []) => ret accu
  | (cons a1 l1, cons a2 l2) => fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) => OCaml.Pervasives.invalid_arg "List.fold_left2" % string
  end.

Fixpoint fold_right2 {A B C : Type}
  (f : A -> B -> C -> C) (l1 : list A) (l2 : list B) (accu : C)
  : M [ OCaml.Invalid_argument ] C :=
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

Fixpoint find {A : Type} (p : A -> bool) (x : list A)
  : M [ OCaml.Not_found ] A :=
  match x with
  | [] => OCaml.raise_Not_found tt
  | cons x l =>
    if p x then
      ret x
    else
      find p l
  end.

Definition find_all {A : Type} (p : A -> bool) : (list A) -> list A :=
  let fix find_coq_rec (accu : list A) (x : list A) : list A :=
    match x with
    | [] => rev accu
    | cons x l =>
      if p x then
        find_coq_rec (cons x accu) l
      else
        find_coq_rec accu l
    end in
  find_coq_rec [].

Definition filter {A : Type} : (A -> bool) -> (list A) -> list A := find_all.

Definition partition {A : Type} (p : A -> bool) (l : list A)
  : (list A) * (list A) :=
  let fix part_coq_rec (yes : list A) (no : list A) (x : list A)
    : (list A) * (list A) :=
    match x with
    | [] => ((rev yes), (rev no))
    | cons x l =>
      if p x then
        part_coq_rec (cons x yes) no l
      else
        part_coq_rec yes (cons x no) l
    end in
  part_coq_rec [] [] l.

Fixpoint split {A B : Type} (x : list (A * B)) : (list A) * (list B) :=
  match x with
  | [] => ([], [])
  | cons (x, y) l =>
    match split l with
    | (rx, ry) => ((cons x rx), (cons y ry))
    end
  end.

Fixpoint combine {A B : Type} (l1 : list A) (l2 : list B)
  : M [ OCaml.Invalid_argument ] (list (A * B)) :=
  match (l1, l2) with
  | ([], []) => ret []
  | (cons a1 l1, cons a2 l2) =>
    let! x := combine l1 l2 in
    ret (cons (a1, a2) x)
  | (_, _) => OCaml.Pervasives.invalid_arg "List.combine" % string
  end.

Fixpoint merge {A : Type} (cmp : A -> A -> Z) (l1 : list A) (l2 : list A)
  : list A :=
  let fix rev_merge_aux_coq_rec (l2 : list A) : list A :=
    match (l1, l2) with
    | ([], l2) => l2
    | (l1, []) => l1
    | (cons h1 t1, cons h2 t2) =>
      if OCaml.Pervasives.le (cmp h1 h2) 0 then
        cons h1 (merge cmp t1 l2)
      else
        cons h2 (rev_merge_aux_coq_rec t2)
    end in
  rev_merge_aux_coq_rec l2.

Fixpoint chop {A : Type} (k : Z) (l : list A)
  : M [ OCaml.Assert_failure ] (list A) :=
  if equiv_decb k 0 then
    ret l
  else
    match l with
    | cons x t => chop (Z.sub k 1) t
    | _ => OCaml.assert false
    end.

Module StableSort.
  Fixpoint rev_merge {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_aux_coq_rec (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        if OCaml.Pervasives.le (cmp h1 h2) 0 then
          rev_merge cmp t1 l2 (cons h1 accu)
        else
          rev_merge_aux_coq_rec t2 (cons h2 accu)
      end in
    rev_merge_aux_coq_rec l2 accu.
  
  Fixpoint rev_merge_rev {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_rev_aux_coq_rec (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        if OCaml.Pervasives.gt (cmp h1 h2) 0 then
          rev_merge_rev cmp t1 l2 (cons h1 accu)
        else
          rev_merge_rev_aux_coq_rec t2 (cons h2 accu)
      end in
    rev_merge_rev_aux_coq_rec l2 accu.
  
  Fixpoint sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ NonTermination; OCaml.Assert_failure ] (list A) :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) =>
        ret
          (if OCaml.Pervasives.le (cmp x1 x2) 0 then
            cons x1 (cons x2 [])
          else
            cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) =>
        ret
          (if OCaml.Pervasives.le (cmp x1 x2) 0 then
            if OCaml.Pervasives.le (cmp x2 x3) 0 then
              cons x1 (cons x2 (cons x3 []))
            else
              if OCaml.Pervasives.le (cmp x1 x3) 0 then
                cons x1 (cons x3 (cons x2 []))
              else
                cons x3 (cons x1 (cons x2 []))
          else
            if OCaml.Pervasives.le (cmp x1 x3) 0 then
              cons x2 (cons x1 (cons x3 []))
            else
              if OCaml.Pervasives.le (cmp x2 x3) 0 then
                cons x2 (cons x3 (cons x1 []))
              else
                cons x3 (cons x2 (cons x1 [])))
      | (n, l) =>
        let n1 := Z.div n 2 in
        let n2 := Z.sub n n1 in
        let! l2 := lift [_;_] "01" (chop n1 l) in
        let! s1 := (rev_sort_rec counter) cmp n1 l in
        let! s2 := (rev_sort_rec counter) cmp n2 l2 in
        ret (rev_merge_rev cmp s1 s2 [])
      end
    end
  
  with rev_sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ NonTermination; OCaml.Assert_failure ] (list A) :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) =>
        ret
          (if OCaml.Pervasives.gt (cmp x1 x2) 0 then
            cons x1 (cons x2 [])
          else
            cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) =>
        ret
          (if OCaml.Pervasives.gt (cmp x1 x2) 0 then
            if OCaml.Pervasives.gt (cmp x2 x3) 0 then
              cons x1 (cons x2 (cons x3 []))
            else
              if OCaml.Pervasives.gt (cmp x1 x3) 0 then
                cons x1 (cons x3 (cons x2 []))
              else
                cons x3 (cons x1 (cons x2 []))
          else
            if OCaml.Pervasives.gt (cmp x1 x3) 0 then
              cons x2 (cons x1 (cons x3 []))
            else
              if OCaml.Pervasives.gt (cmp x2 x3) 0 then
                cons x2 (cons x3 (cons x1 []))
              else
                cons x3 (cons x2 (cons x1 [])))
      | (n, l) =>
        let n1 := Z.div n 2 in
        let n2 := Z.sub n n1 in
        let! l2 := lift [_;_] "01" (chop n1 l) in
        let! s1 := (sort_rec counter) cmp n1 l in
        let! s2 := (sort_rec counter) cmp n2 l2 in
        ret (rev_merge cmp s1 s2 [])
      end
    end.
  
  Definition sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
    let! x := lift [_;_;_] "100" (read_counter tt) in
    lift [_;_;_] "011" (sort_rec x cmp n l).
  
  Definition rev_sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
    let! x := lift [_;_;_] "100" (read_counter tt) in
    lift [_;_;_] "011" (rev_sort_rec x cmp n l).
End StableSort.

Definition stable_sort {A : Type} (cmp : A -> A -> Z) (l : list A)
  : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
  let len := length l in
  if OCaml.Pervasives.lt len 2 then
    ret l
  else
    StableSort.sort cmp len l.

Definition sort {A : Type}
  : (A -> A -> Z) ->
    (list A) -> M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
  stable_sort.

Definition fast_sort {A : Type}
  : (A -> A -> Z) ->
    (list A) -> M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
  stable_sort.

Module SortUniq.
  Fixpoint rev_merge {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_aux_coq_rec (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        let c := cmp h1 h2 in
        if equiv_decb c 0 then
          rev_merge cmp t1 t2 (cons h1 accu)
        else
          if OCaml.Pervasives.lt c 0 then
            rev_merge cmp t1 l2 (cons h1 accu)
          else
            rev_merge_aux_coq_rec t2 (cons h2 accu)
      end in
    rev_merge_aux_coq_rec l2 accu.
  
  Fixpoint rev_merge_rev {A : Type}
    (cmp : A -> A -> Z) (l1 : list A) (l2 : list A) (accu : list A) : list A :=
    let fix rev_merge_rev_aux_coq_rec (l2 : list A) (accu : list A) : list A :=
      match (l1, l2) with
      | ([], l2) => rev_append l2 accu
      | (l1, []) => rev_append l1 accu
      | (cons h1 t1, cons h2 t2) =>
        let c := cmp h1 h2 in
        if equiv_decb c 0 then
          rev_merge_rev cmp t1 t2 (cons h1 accu)
        else
          if OCaml.Pervasives.gt c 0 then
            rev_merge_rev cmp t1 l2 (cons h1 accu)
          else
            rev_merge_rev_aux_coq_rec t2 (cons h2 accu)
      end in
    rev_merge_rev_aux_coq_rec l2 accu.
  
  Fixpoint sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ NonTermination; OCaml.Assert_failure ] (list A) :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) =>
        ret
          (let c := cmp x1 x2 in
          if equiv_decb c 0 then
            cons x1 []
          else
            if OCaml.Pervasives.lt c 0 then
              cons x1 (cons x2 [])
            else
              cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) =>
        ret
          (let c := cmp x1 x2 in
          if equiv_decb c 0 then
            let c := cmp x2 x3 in
            if equiv_decb c 0 then
              cons x2 []
            else
              if OCaml.Pervasives.lt c 0 then
                cons x2 (cons x3 [])
              else
                cons x3 (cons x2 [])
          else
            if OCaml.Pervasives.lt c 0 then
              let c := cmp x2 x3 in
              if equiv_decb c 0 then
                cons x1 (cons x2 [])
              else
                if OCaml.Pervasives.lt c 0 then
                  cons x1 (cons x2 (cons x3 []))
                else
                  let c := cmp x1 x3 in
                  if equiv_decb c 0 then
                    cons x1 (cons x2 [])
                  else
                    if OCaml.Pervasives.lt c 0 then
                      cons x1 (cons x3 (cons x2 []))
                    else
                      cons x3 (cons x1 (cons x2 []))
            else
              let c := cmp x1 x3 in
              if equiv_decb c 0 then
                cons x2 (cons x1 [])
              else
                if OCaml.Pervasives.lt c 0 then
                  cons x2 (cons x1 (cons x3 []))
                else
                  let c := cmp x2 x3 in
                  if equiv_decb c 0 then
                    cons x2 (cons x1 [])
                  else
                    if OCaml.Pervasives.lt c 0 then
                      cons x2 (cons x3 (cons x1 []))
                    else
                      cons x3 (cons x2 (cons x1 [])))
      | (n, l) =>
        let n1 := Z.div n 2 in
        let n2 := Z.sub n n1 in
        let! l2 := lift [_;_] "01" (chop n1 l) in
        let! s1 := (rev_sort_rec counter) cmp n1 l in
        let! s2 := (rev_sort_rec counter) cmp n2 l2 in
        ret (rev_merge_rev cmp s1 s2 [])
      end
    end
  
  with rev_sort_rec {A : Type}
    (counter : nat) (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ NonTermination; OCaml.Assert_failure ] (list A) :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      match (n, l) with
      | (2, cons x1 (cons x2 _)) =>
        ret
          (let c := cmp x1 x2 in
          if equiv_decb c 0 then
            cons x1 []
          else
            if OCaml.Pervasives.gt c 0 then
              cons x1 (cons x2 [])
            else
              cons x2 (cons x1 []))
      | (3, cons x1 (cons x2 (cons x3 _))) =>
        ret
          (let c := cmp x1 x2 in
          if equiv_decb c 0 then
            let c := cmp x2 x3 in
            if equiv_decb c 0 then
              cons x2 []
            else
              if OCaml.Pervasives.gt c 0 then
                cons x2 (cons x3 [])
              else
                cons x3 (cons x2 [])
          else
            if OCaml.Pervasives.gt c 0 then
              let c := cmp x2 x3 in
              if equiv_decb c 0 then
                cons x1 (cons x2 [])
              else
                if OCaml.Pervasives.gt c 0 then
                  cons x1 (cons x2 (cons x3 []))
                else
                  let c := cmp x1 x3 in
                  if equiv_decb c 0 then
                    cons x1 (cons x2 [])
                  else
                    if OCaml.Pervasives.gt c 0 then
                      cons x1 (cons x3 (cons x2 []))
                    else
                      cons x3 (cons x1 (cons x2 []))
            else
              let c := cmp x1 x3 in
              if equiv_decb c 0 then
                cons x2 (cons x1 [])
              else
                if OCaml.Pervasives.gt c 0 then
                  cons x2 (cons x1 (cons x3 []))
                else
                  let c := cmp x2 x3 in
                  if equiv_decb c 0 then
                    cons x2 (cons x1 [])
                  else
                    if OCaml.Pervasives.gt c 0 then
                      cons x2 (cons x3 (cons x1 []))
                    else
                      cons x3 (cons x2 (cons x1 [])))
      | (n, l) =>
        let n1 := Z.div n 2 in
        let n2 := Z.sub n n1 in
        let! l2 := lift [_;_] "01" (chop n1 l) in
        let! s1 := (sort_rec counter) cmp n1 l in
        let! s2 := (sort_rec counter) cmp n2 l2 in
        ret (rev_merge cmp s1 s2 [])
      end
    end.
  
  Definition sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
    let! x := lift [_;_;_] "100" (read_counter tt) in
    lift [_;_;_] "011" (sort_rec x cmp n l).
  
  Definition rev_sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A)
    : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
    let! x := lift [_;_;_] "100" (read_counter tt) in
    lift [_;_;_] "011" (rev_sort_rec x cmp n l).
End SortUniq.

Definition sort_uniq {A : Type} (cmp : A -> A -> Z) (l : list A)
  : M [ Counter; NonTermination; OCaml.Assert_failure ] (list A) :=
  let len := length l in
  if OCaml.Pervasives.lt len 2 then
    ret l
  else
    SortUniq.sort cmp len l.
