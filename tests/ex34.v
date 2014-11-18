Require Import CoqOfOCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Module Ord.
  Parameter t : Type.
  
  Definition compare (x : t) : t -> Z :=
    match x with
    | _ =>
      fun x_1 =>
        match x_1 with
        | _ => 0
        end
    end.
End Ord.

Definition elt := Ord.t.

Inductive t : Type :=
| Empty : t
| Node : t -> elt -> t -> Z -> t.

Definition height (x : t) : Z :=
  match x with
  | Empty => 0
  | Node _ _ _ h => h
  end.

Definition create (l : t) (v : elt) (r : t) : t :=
  let hl :=
    match l with
    | Empty => 0
    | Node _ _ _ h => h
    end in
  let hr :=
    match r with
    | Empty => 0
    | Node _ _ _ h => h
    end in
  Node l v r
    (if OCaml.Pervasives.ge hl hr then
      Z.add hl 1
    else
      Z.add hr 1).

Definition bal (l : t) (v : elt) (r : t) : M [ OCaml.Invalid_argument ] t :=
  let hl :=
    match l with
    | Empty => 0
    | Node _ _ _ h => h
    end in
  let hr :=
    match r with
    | Empty => 0
    | Node _ _ _ h => h
    end in
  if OCaml.Pervasives.gt hl (Z.add hr 2) then
    match l with
    | Empty => OCaml.Pervasives.invalid_arg "Set.bal" % string
    | Node ll lv lr _ =>
      if OCaml.Pervasives.ge (height ll) (height lr) then
        ret (create ll lv (create lr v r))
      else
        match lr with
        | Empty => OCaml.Pervasives.invalid_arg "Set.bal" % string
        | Node lrl lrv lrr _ =>
          ret (create (create ll lv lrl) lrv (create lrr v r))
        end
    end
  else
    if OCaml.Pervasives.gt hr (Z.add hl 2) then
      match r with
      | Empty => OCaml.Pervasives.invalid_arg "Set.bal" % string
      | Node rl rv rr _ =>
        if OCaml.Pervasives.ge (height rr) (height rl) then
          ret (create (create l v rl) rv rr)
        else
          match rl with
          | Empty => OCaml.Pervasives.invalid_arg "Set.bal" % string
          | Node rll rlv rlr _ =>
            ret (create (create l v rll) rlv (create rlr rv rr))
          end
      end
    else
      ret
        (Node l v r
          (if OCaml.Pervasives.ge hl hr then
            Z.add hl 1
          else
            Z.add hr 1)).

Fixpoint add (x : elt) (x_1 : t) : M [ OCaml.Invalid_argument ] t :=
  match x_1 with
  | Empty => ret (Node Empty x Empty 1)
  | Node l v r _ as t =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret t
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := add x l in
        bal x_2 v r
      else
        let! x_2 := add x r in
        bal l v x_2
  end.

Definition singleton (x : elt) : t := Node Empty x Empty 1.

Fixpoint add_min_element (v : elt) (x : t) : M [ OCaml.Invalid_argument ] t :=
  match x with
  | Empty => ret (singleton v)
  | Node l x r h =>
    let! x_1 := add_min_element v l in
    bal x_1 x r
  end.

Fixpoint add_max_element (v : elt) (x : t) : M [ OCaml.Invalid_argument ] t :=
  match x with
  | Empty => ret (singleton v)
  | Node l x r h =>
    let! x_1 := add_max_element v r in
    bal l x x_1
  end.

Fixpoint join_rec (counter : nat) (l : t) (v : elt) (r : t)
  : M [ NonTermination; OCaml.Invalid_argument ] t :=
  match counter with
  | O => lift [_;_] "10" (not_terminated tt)
  | S counter =>
    match (l, r) with
    | (Empty, _) => lift [_;_] "01" (add_min_element v r)
    | (_, Empty) => lift [_;_] "01" (add_max_element v l)
    | (Node ll lv lr lh, Node rl rv rr rh) =>
      if OCaml.Pervasives.gt lh (Z.add rh 2) then
        let! x := (join_rec counter) lr v r in
        lift [_;_] "01" (bal ll lv x)
      else
        if OCaml.Pervasives.gt rh (Z.add lh 2) then
          let! x := (join_rec counter) l v rl in
          lift [_;_] "01" (bal x rv rr)
        else
          ret (create l v r)
    end
  end.

Definition join (l : t) (v : elt) (r : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ] t :=
  let! x := lift [_;_;_] "100" (read_counter tt) in
  lift [_;_;_] "011" (join_rec x l v r).

Fixpoint min_elt (x : t) : M [ OCaml.Not_found ] elt :=
  match x with
  | Empty => OCaml.raise_Not_found tt
  | Node Empty v r _ => ret v
  | Node l v r _ => min_elt l
  end.

Fixpoint max_elt (x : t) : M [ OCaml.Not_found ] elt :=
  match x with
  | Empty => OCaml.raise_Not_found tt
  | Node l v Empty _ => ret v
  | Node l v r _ => max_elt r
  end.

Fixpoint remove_min_elt (x : t) : M [ OCaml.Invalid_argument ] t :=
  match x with
  | Empty => OCaml.Pervasives.invalid_arg "Set.remove_min_elt" % string
  | Node Empty v r _ => ret r
  | Node l v r _ =>
    let! x_1 := remove_min_elt l in
    bal x_1 v r
  end.

Definition merge (t1 : t) (t2 : t)
  : M [ OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match (t1, t2) with
  | (Empty, t) => ret t
  | (t, Empty) => ret t
  | (_, _) =>
    let! x := lift [_;_] "01" (min_elt t2) in
    let! x_1 := lift [_;_] "10" (remove_min_elt t2) in
    lift [_;_] "10" (bal t1 x x_1)
  end.

Definition concat (t1 : t) (t2 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match (t1, t2) with
  | (Empty, t) => ret t
  | (t, Empty) => ret t
  | (_, _) =>
    let! x := lift [_;_;_;_] "0001" (min_elt t2) in
    let! x_1 := lift [_;_;_;_] "0010" (remove_min_elt t2) in
    lift [_;_;_;_] "1110" (join t1 x x_1)
  end.

Fixpoint split (x : Ord.t) (x_1 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ] (t * bool * t) :=
  match x_1 with
  | Empty => ret (Empty, false, Empty)
  | Node l v r _ =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret (l, true, r)
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := split x l in
        match x_2 with
        | (ll, pres, rl) =>
          let! x_2 := join rl v r in
          ret (ll, pres, x_2)
        end
      else
        let! x_2 := split x r in
        match x_2 with
        | (lr, pres, rr) =>
          let! x_2 := join l v lr in
          ret (x_2, pres, rr)
        end
  end.

Definition empty : t := Empty.

Definition is_empty (x : t) : bool :=
  match x with
  | Empty => true
  | _ => false
  end.

Fixpoint mem (x : Ord.t) (x_1 : t) : bool :=
  match x_1 with
  | Empty => false
  | Node l v r _ =>
    let c := Ord.compare x v in
    orb (equiv_decb c 0)
      (mem x
        (if OCaml.Pervasives.lt c 0 then
          l
        else
          r))
  end.

Fixpoint remove (x : Ord.t) (x_1 : t)
  : M [ OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match x_1 with
  | Empty => ret Empty
  | Node l v r _ =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      merge l r
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := remove x l in
        lift [_;_] "10" (bal x_2 v r)
      else
        let! x_2 := remove x r in
        lift [_;_] "10" (bal l v x_2)
  end.

Fixpoint union_rec (counter : nat) (s1 : t) (s2 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ] t :=
  match counter with
  | O => lift [_;_;_] "010" (not_terminated tt)
  | S counter =>
    match (s1, s2) with
    | (Empty, t2) => ret t2
    | (t1, Empty) => ret t1
    | (Node l1 v1 r1 h1, Node l2 v2 r2 h2) =>
      if OCaml.Pervasives.ge h1 h2 then
        if equiv_decb h2 1 then
          lift [_;_;_] "001" (add v2 s1)
        else
          let! x := split v1 s2 in
          match x with
          | (l2, _, r2) =>
            let! x := (union_rec counter) l1 l2 in
            let! x_1 := (union_rec counter) r1 r2 in
            join x v1 x_1
          end
      else
        if equiv_decb h1 1 then
          lift [_;_;_] "001" (add v1 s2)
        else
          let! x := split v2 s1 in
          match x with
          | (l1, _, r1) =>
            let! x := (union_rec counter) l1 l2 in
            let! x_1 := (union_rec counter) r1 r2 in
            join x v2 x_1
          end
    end
  end.

Definition union (s1 : t) (s2 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ] t :=
  let! x := lift [_;_;_] "100" (read_counter tt) in
  union_rec x s1 s2.

Fixpoint inter (s1 : t) (s2 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match (s1, s2) with
  | (Empty, t2) => ret Empty
  | (t1, Empty) => ret Empty
  | (Node l1 v1 r1 _, t2) =>
    let! x := lift [_;_;_;_] "1110" (split v1 t2) in
    match x with
    | (l2, false, r2) =>
      let! x := inter l1 l2 in
      let! x_1 := inter r1 r2 in
      concat x x_1
    | (l2, true, r2) =>
      let! x := inter l1 l2 in
      let! x_1 := inter r1 r2 in
      lift [_;_;_;_] "1110" (join x v1 x_1)
    end
  end.

Fixpoint diff (s1 : t) (s2 : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match (s1, s2) with
  | (Empty, t2) => ret Empty
  | (t1, Empty) => ret t1
  | (Node l1 v1 r1 _, t2) =>
    let! x := lift [_;_;_;_] "1110" (split v1 t2) in
    match x with
    | (l2, false, r2) =>
      let! x := diff l1 l2 in
      let! x_1 := diff r1 r2 in
      lift [_;_;_;_] "1110" (join x v1 x_1)
    | (l2, true, r2) =>
      let! x := diff l1 l2 in
      let! x_1 := diff r1 r2 in
      concat x x_1
    end
  end.

Inductive enumeration : Type :=
| End : enumeration
| More : elt -> t -> enumeration -> enumeration.

Fixpoint cons_enum (s : t) (e : enumeration) : enumeration :=
  match s with
  | Empty => e
  | Node l v r _ => cons_enum l (More v r e)
  end.

Fixpoint compare_aux_rec (counter : nat) (e1 : enumeration) (e2 : enumeration)
  : M [ NonTermination ] Z :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match (e1, e2) with
    | (End, End) => ret 0
    | (End, _) => ret (-1)
    | (_, End) => ret 1
    | (More v1 r1 e1, More v2 r2 e2) =>
      let c := Ord.compare v1 v2 in
      if nequiv_decb c 0 then
        ret c
      else
        (compare_aux_rec counter) (cons_enum r1 e1) (cons_enum r2 e2)
    end
  end.

Definition compare_aux (e1 : enumeration) (e2 : enumeration)
  : M [ Counter; NonTermination ] Z :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (compare_aux_rec x e1 e2).

Definition compare (s1 : t) (s2 : t) : M [ Counter; NonTermination ] Z :=
  compare_aux (cons_enum s1 End) (cons_enum s2 End).

Definition equal (s1 : t) (s2 : t) : M [ Counter; NonTermination ] bool :=
  let! x := compare s1 s2 in
  ret (equiv_decb x 0).

Fixpoint subset_rec (counter : nat) (s1 : t) (s2 : t)
  : M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match (s1, s2) with
    | (Empty, _) => ret true
    | (_, Empty) => ret false
    | (Node l1 v1 r1 _, Node l2 v2 r2 _ as t2) =>
      let c := Ord.compare v1 v2 in
      if equiv_decb c 0 then
        let! x := (subset_rec counter) l1 l2 in
        let! x_1 := (subset_rec counter) r1 r2 in
        ret (andb x x_1)
      else
        if OCaml.Pervasives.lt c 0 then
          let! x := (subset_rec counter) (Node l1 v1 Empty 0) l2 in
          let! x_1 := (subset_rec counter) r1 t2 in
          ret (andb x x_1)
        else
          let! x := (subset_rec counter) (Node Empty v1 r1 0) r2 in
          let! x_1 := (subset_rec counter) l1 t2 in
          ret (andb x x_1)
    end
  end.

Definition subset (s1 : t) (s2 : t) : M [ Counter; NonTermination ] bool :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (subset_rec x s1 s2).

Fixpoint iter {A : Type} (f : elt -> A) (x : t) : unit :=
  match x with
  | Empty => tt
  | Node l v r _ => iter f r
  end.

Fixpoint fold {A : Type} (f : elt -> A -> A) (s : t) (accu : A) : A :=
  match s with
  | Empty => accu
  | Node l v r _ => fold f r (f v (fold f l accu))
  end.

Fixpoint for_all (p : elt -> bool) (x : t) : bool :=
  match x with
  | Empty => true
  | Node l v r _ => andb (p v) (andb (for_all p l) (for_all p r))
  end.

Fixpoint exists_ (p : elt -> bool) (x : t) : bool :=
  match x with
  | Empty => false
  | Node l v r _ => orb (p v) (orb (exists_ p l) (exists_ p r))
  end.

Fixpoint filter (p : elt -> bool) (x : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] t :=
  match x with
  | Empty => ret Empty
  | Node l v r _ =>
    let! l' := filter p l in
    let pv := p v in
    let! r' := filter p r in
    if pv then
      lift [_;_;_;_] "1110" (join l' v r')
    else
      concat l' r'
  end.

Fixpoint partition (p : elt -> bool) (x : t)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ]
    (t * t) :=
  match x with
  | Empty => ret (Empty, Empty)
  | Node l v r _ =>
    let! x_1 := partition p l in
    match x_1 with
    | (lt, lf) =>
      let pv := p v in
      let! x_1 := partition p r in
      match x_1 with
      | (rt, rf) =>
        if pv then
          let! x_1 := lift [_;_;_;_] "1110" (join lt v rt) in
          let! x_2 := concat lf rf in
          ret (x_1, x_2)
        else
          let! x_1 := concat lt rt in
          let! x_2 := lift [_;_;_;_] "1110" (join lf v rf) in
          ret (x_1, x_2)
      end
    end
  end.

Fixpoint cardinal (x : t) : Z :=
  match x with
  | Empty => 0
  | Node l v r _ => Z.add (Z.add (cardinal l) 1) (cardinal r)
  end.

Fixpoint elements_aux (accu : list elt) (x : t) : list elt :=
  match x with
  | Empty => accu
  | Node l v r _ => elements_aux (cons v (elements_aux accu r)) l
  end.

Definition elements (s : t) : list elt := elements_aux [] s.

Definition choose : t -> M [ OCaml.Not_found ] elt := min_elt.

Fixpoint find (x : Ord.t) (x_1 : t) : M [ OCaml.Not_found ] elt :=
  match x_1 with
  | Empty => OCaml.raise_Not_found tt
  | Node l v r _ =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret v
    else
      find x
        (if OCaml.Pervasives.lt c 0 then
          l
        else
          r)
  end.

Definition of_sorted_list (l : list elt)
  : M [ Counter; NonTermination; OCaml.Assert_failure ] t :=
  let fix sub_rec (counter : nat) (n : Z) (l : list elt)
    : M [ NonTermination; OCaml.Assert_failure ] (t * (list elt)) :=
    match counter with
    | O => lift [_;_] "10" (not_terminated tt)
    | S counter =>
      match (n, l) with
      | (0, l) => ret (Empty, l)
      | (1, cons x0 l) => ret ((Node Empty x0 Empty 1), l)
      | (2, cons x0 (cons x1 l)) =>
        ret ((Node (Node Empty x0 Empty 1) x1 Empty 2), l)
      | (3, cons x0 (cons x1 (cons x2 l))) =>
        ret ((Node (Node Empty x0 Empty 1) x1 (Node Empty x2 Empty 1) 2), l)
      | (n, l) =>
        let nl := Z.div n 2 in
        let! x := (sub_rec counter) nl l in
        match x with
        | (left_, l) =>
          match l with
          | [] => lift [_;_] "01" (OCaml.assert false)
          | cons mid l =>
            let! x := (sub_rec counter) (Z.sub (Z.sub n nl) 1) l in
            match x with
            | (right_, l) => ret ((create left_ mid right_), l)
            end
          end
        end
      end
    end in
  let sub (n : Z) (l : list elt)
    : M [ Counter; NonTermination; OCaml.Assert_failure ] (t * (list elt)) :=
    let! x := lift [_;_;_] "100" (read_counter tt) in
    lift [_;_;_] "011" (sub_rec x n l) in
  let! x := sub (OCaml.List.length l) l in
  ret (fst x).
