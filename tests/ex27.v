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

Fixpoint chop {A : Type} (k : Z) (l : list A) : list A :=
  if equiv_decb k 0 then
    l
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
  
  Fixpoint sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A) : list A :=
    match (n, l) with
    | (2, cons x1 (cons x2 _)) =>
      if OCaml.Pervasives.le (cmp x1 x2) 0 then
        cons x1 (cons x2 [])
      else
        cons x2 (cons x1 [])
    | (3, cons x1 (cons x2 (cons x3 _))) =>
      if OCaml.Pervasives.le (cmp x1 x2) 0 then
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
            cons x3 (cons x2 (cons x1 []))
    | (n, l) =>
      let n1 := Z.div n 2 in
      let n2 := Z.sub n n1 in
      let l2 := chop n1 l in
      let s1 := rev_sort cmp n1 l in
      let s2 := rev_sort cmp n2 l2 in
      rev_merge_rev cmp s1 s2 []
    end
  
  with rev_sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A) : list A :=
    match (n, l) with
    | (2, cons x1 (cons x2 _)) =>
      if OCaml.Pervasives.gt (cmp x1 x2) 0 then
        cons x1 (cons x2 [])
      else
        cons x2 (cons x1 [])
    | (3, cons x1 (cons x2 (cons x3 _))) =>
      if OCaml.Pervasives.gt (cmp x1 x2) 0 then
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
            cons x3 (cons x2 (cons x1 []))
    | (n, l) =>
      let n1 := Z.div n 2 in
      let n2 := Z.sub n n1 in
      let l2 := chop n1 l in
      let s1 := sort cmp n1 l in
      let s2 := sort cmp n2 l2 in
      rev_merge cmp s1 s2 []
    end.
End StableSort.

Definition stable_sort {A : Type} (cmp : A -> A -> Z) (l : list A) : list A :=
  let len := length l in
  if OCaml.Pervasives.lt len 2 then
    l
  else
    StableSort.sort cmp len l.

Definition sort {A : Type} : (A -> A -> Z) -> (list A) -> list A := stable_sort.

Definition fast_sort {A : Type} : (A -> A -> Z) -> (list A) -> list A :=
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
  
  Fixpoint sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A) : list A :=
    match (n, l) with
    | (2, cons x1 (cons x2 _)) =>
      let c := cmp x1 x2 in
      if equiv_decb c 0 then
        cons x1 []
      else
        if OCaml.Pervasives.lt c 0 then
          cons x1 (cons x2 [])
        else
          cons x2 (cons x1 [])
    | (3, cons x1 (cons x2 (cons x3 _))) =>
      let c := cmp x1 x2 in
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
                  cons x3 (cons x2 (cons x1 []))
    | (n, l) =>
      let n1 := Z.div n 2 in
      let n2 := Z.sub n n1 in
      let l2 := chop n1 l in
      let s1 := rev_sort cmp n1 l in
      let s2 := rev_sort cmp n2 l2 in
      rev_merge_rev cmp s1 s2 []
    end
  
  with rev_sort {A : Type} (cmp : A -> A -> Z) (n : Z) (l : list A) : list A :=
    match (n, l) with
    | (2, cons x1 (cons x2 _)) =>
      let c := cmp x1 x2 in
      if equiv_decb c 0 then
        cons x1 []
      else
        if OCaml.Pervasives.gt c 0 then
          cons x1 (cons x2 [])
        else
          cons x2 (cons x1 [])
    | (3, cons x1 (cons x2 (cons x3 _))) =>
      let c := cmp x1 x2 in
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
                  cons x3 (cons x2 (cons x1 []))
    | (n, l) =>
      let n1 := Z.div n 2 in
      let n2 := Z.sub n n1 in
      let l2 := chop n1 l in
      let s1 := sort cmp n1 l in
      let s2 := sort cmp n2 l2 in
      rev_merge cmp s1 s2 []
    end.
End SortUniq.

Definition sort_uniq {A : Type} (cmp : A -> A -> Z) (l : list A) : list A :=
  let len := length l in
  if OCaml.Pervasives.lt len 2 then
    l
  else
    SortUniq.sort cmp len l.
