Require Import OCaml.OCaml.

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

Definition key := Ord.t.

Inductive t (a : Type) : Type :=
| Empty : t a
| Node : (t a) -> key -> a -> (t a) -> Z -> t a.
Arguments Empty {a}.
Arguments Node {a} _ _ _ _ _.

Definition height {A : Type} (x : t A) : Z :=
  match x with
  | Empty => 0
  | Node _ _ _ _ h => h
  end.

Definition create {A : Type} (l : t A) (x : key) (d : A) (r : t A) : t A :=
  let hl := height l in
  let hr := height r in
  Node l x d r
    (if OCaml.Pervasives.ge hl hr then
      Z.add hl 1
    else
      Z.add hr 1).

Definition singleton {A : Type} (x : key) (d : A) : t A :=
  Node Empty x d Empty 1.

Definition bal {A : Type} (l : t A) (x : key) (d : A) (r : t A)
  : M [ OCaml.Invalid_argument ] (t A) :=
  let hl :=
    match l with
    | Empty => 0
    | Node _ _ _ _ h => h
    end in
  let hr :=
    match r with
    | Empty => 0
    | Node _ _ _ _ h => h
    end in
  if OCaml.Pervasives.gt hl (Z.add hr 2) then
    match l with
    | Empty => OCaml.Pervasives.invalid_arg "Map.bal" % string
    | Node ll lv ld lr _ =>
      if OCaml.Pervasives.ge (height ll) (height lr) then
        ret (create ll lv ld (create lr x d r))
      else
        match lr with
        | Empty => OCaml.Pervasives.invalid_arg "Map.bal" % string
        | Node lrl lrv lrd lrr _ =>
          ret (create (create ll lv ld lrl) lrv lrd (create lrr x d r))
        end
    end
  else
    if OCaml.Pervasives.gt hr (Z.add hl 2) then
      match r with
      | Empty => OCaml.Pervasives.invalid_arg "Map.bal" % string
      | Node rl rv rd rr _ =>
        if OCaml.Pervasives.ge (height rr) (height rl) then
          ret (create (create l x d rl) rv rd rr)
        else
          match rl with
          | Empty => OCaml.Pervasives.invalid_arg "Map.bal" % string
          | Node rll rlv rld rlr _ =>
            ret (create (create l x d rll) rlv rld (create rlr rv rd rr))
          end
      end
    else
      ret
        (Node l x d r
          (if OCaml.Pervasives.ge hl hr then
            Z.add hl 1
          else
            Z.add hr 1)).

Definition empty {A : Type} : t A := Empty.

Definition is_empty {A : Type} (x : t A) : bool :=
  match x with
  | Empty => true
  | _ => false
  end.

Fixpoint add {A : Type} (x : key) (data : A) (x_1 : t A)
  : M [ OCaml.Invalid_argument ] (t A) :=
  match x_1 with
  | Empty => ret (Node Empty x data Empty 1)
  | Node l v d r h =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret (Node l x data r h)
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := add x data l in
        bal x_2 v d r
      else
        let! x_2 := add x data r in
        bal l v d x_2
  end.

Fixpoint find {A : Type} (x : Ord.t) (x_1 : t A) : M [ OCaml.Not_found ] A :=
  match x_1 with
  | Empty => OCaml.raise_Not_found tt
  | Node l v d r _ =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret d
    else
      find x
        (if OCaml.Pervasives.lt c 0 then
          l
        else
          r)
  end.

Fixpoint mem {A : Type} (x : Ord.t) (x_1 : t A) : bool :=
  match x_1 with
  | Empty => false
  | Node l v d r _ =>
    let c := Ord.compare x v in
    orb (equiv_decb c 0)
      (mem x
        (if OCaml.Pervasives.lt c 0 then
          l
        else
          r))
  end.

Fixpoint min_binding {A : Type} (x : t A) : M [ OCaml.Not_found ] (key * A) :=
  match x with
  | Empty => OCaml.raise_Not_found tt
  | Node Empty x d r _ => ret (x, d)
  | Node l x d r _ => min_binding l
  end.

Fixpoint max_binding {A : Type} (x : t A) : M [ OCaml.Not_found ] (key * A) :=
  match x with
  | Empty => OCaml.raise_Not_found tt
  | Node l x d Empty _ => ret (x, d)
  | Node l x d r _ => max_binding r
  end.

Fixpoint remove_min_binding {A : Type} (x : t A)
  : M [ OCaml.Invalid_argument ] (t A) :=
  match x with
  | Empty => OCaml.Pervasives.invalid_arg "Map.remove_min_elt" % string
  | Node Empty x d r _ => ret r
  | Node l x d r _ =>
    let! x_1 := remove_min_binding l in
    bal x_1 x d r
  end.

Definition remove_merge {A : Type} (t1 : t A) (t2 : t A)
  : M [ OCaml.Invalid_argument; OCaml.Not_found ] (t A) :=
  match (t1, t2) with
  | (Empty, t) => ret t
  | (t, Empty) => ret t
  | (_, _) =>
    let! x := lift [_;_] "01" (min_binding t2) in
    match x with
    | (x, d) =>
      lift [_;_] "10"
        (let! x_1 := remove_min_binding t2 in
        bal t1 x d x_1)
    end
  end.

Fixpoint remove {A : Type} (x : Ord.t) (x_1 : t A)
  : M [ OCaml.Invalid_argument; OCaml.Not_found ] (t A) :=
  match x_1 with
  | Empty => ret Empty
  | Node l v d r h =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      remove_merge l r
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := remove x l in
        lift [_;_] "10" (bal x_2 v d r)
      else
        let! x_2 := remove x r in
        lift [_;_] "10" (bal l v d x_2)
  end.

Fixpoint iter {A B : Type} (f : key -> A -> B) (x : t A) : unit :=
  match x with
  | Empty => tt
  | Node l v d r _ => iter f r
  end.

Fixpoint map {A B : Type} (f : A -> B) (x : t A) : t B :=
  match x with
  | Empty => Empty
  | Node l v d r h =>
    let l' := map f l in
    let d' := f d in
    let r' := map f r in
    Node l' v d' r' h
  end.

Fixpoint mapi {A B : Type} (f : key -> A -> B) (x : t A) : t B :=
  match x with
  | Empty => Empty
  | Node l v d r h =>
    let l' := mapi f l in
    let d' := f v d in
    let r' := mapi f r in
    Node l' v d' r' h
  end.

Fixpoint fold {A B : Type} (f : key -> A -> B -> B) (m : t A) (accu : B) : B :=
  match m with
  | Empty => accu
  | Node l v d r _ => fold f r (f v d (fold f l accu))
  end.

Fixpoint for_all {A : Type} (p : key -> A -> bool) (x : t A) : bool :=
  match x with
  | Empty => true
  | Node l v d r _ => andb (p v d) (andb (for_all p l) (for_all p r))
  end.

Fixpoint exists_ {A : Type} (p : key -> A -> bool) (x : t A) : bool :=
  match x with
  | Empty => false
  | Node l v d r _ => orb (p v d) (orb (exists_ p l) (exists_ p r))
  end.

Fixpoint add_min_binding {A : Type} (k : key) (v : A) (x : t A)
  : M [ OCaml.Invalid_argument ] (t A) :=
  match x with
  | Empty => ret (singleton k v)
  | Node l x d r h =>
    let! x_1 := add_min_binding k v l in
    bal x_1 x d r
  end.

Fixpoint add_max_binding {A : Type} (k : key) (v : A) (x : t A)
  : M [ OCaml.Invalid_argument ] (t A) :=
  match x with
  | Empty => ret (singleton k v)
  | Node l x d r h =>
    let! x_1 := add_max_binding k v r in
    bal l x d x_1
  end.

Fixpoint join_rec {A : Type}
  (counter : nat) (l : t A) (v : key) (d : A) (r : t A)
  : M [ NonTermination; OCaml.Invalid_argument ] (t A) :=
  match counter with
  | O => lift [_;_] "10" (not_terminated tt)
  | S counter =>
    match (l, r) with
    | (Empty, _) => lift [_;_] "01" (add_min_binding v d r)
    | (_, Empty) => lift [_;_] "01" (add_max_binding v d l)
    | (Node ll lv ld lr lh, Node rl rv rd rr rh) =>
      if OCaml.Pervasives.gt lh (Z.add rh 2) then
        let! x := (join_rec counter) lr v d r in
        lift [_;_] "01" (bal ll lv ld x)
      else
        if OCaml.Pervasives.gt rh (Z.add lh 2) then
          let! x := (join_rec counter) l v d rl in
          lift [_;_] "01" (bal x rv rd rr)
        else
          ret (create l v d r)
    end
  end.

Definition join {A : Type} (l : t A) (v : key) (d : A) (r : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ] (t A) :=
  let! x := lift [_;_;_] "100" (read_counter tt) in
  lift [_;_;_] "011" (join_rec x l v d r).

Definition concat {A : Type} (t1 : t A) (t2 : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] (t A) :=
  match (t1, t2) with
  | (Empty, t) => ret t
  | (t, Empty) => ret t
  | (_, _) =>
    let! x := lift [_;_;_;_] "0001" (min_binding t2) in
    match x with
    | (x, d) =>
      lift [_;_;_;_] "1110"
        (let! x_1 := lift [_;_;_] "001" (remove_min_binding t2) in
        join t1 x d x_1)
    end
  end.

Definition concat_or_join {A : Type}
  (t1 : t A) (v : key) (d : option A) (t2 : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] (t A) :=
  match d with
  | Some d => lift [_;_;_;_] "1110" (join t1 v d t2)
  | None => concat t1 t2
  end.

Fixpoint split {A : Type} (x : Ord.t) (x_1 : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument ]
    ((t A) * (option A) * (t A)) :=
  match x_1 with
  | Empty => ret (Empty, None, Empty)
  | Node l v d r _ =>
    let c := Ord.compare x v in
    if equiv_decb c 0 then
      ret (l, (Some d), r)
    else
      if OCaml.Pervasives.lt c 0 then
        let! x_2 := split x l in
        match x_2 with
        | (ll, pres, rl) =>
          let! x_2 := join rl v d r in
          ret (ll, pres, x_2)
        end
      else
        let! x_2 := split x r in
        match x_2 with
        | (lr, pres, rr) =>
          let! x_2 := join l v d lr in
          ret (x_2, pres, rr)
        end
  end.

Fixpoint merge_rec {A B C : Type}
  (counter : nat) (f : key -> (option A) -> (option B) -> option C) (s1 : t A)
  (s2 : t B)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] (t C) :=
  match counter with
  | O => lift [_;_;_;_] "0100" (not_terminated tt)
  | S counter =>
    match (s1, s2) with
    | (Empty, Empty) => ret Empty
    | (Node l1 v1 d1 r1 h1, _) =>
      let! x := lift [_;_;_;_] "1110" (split v1 s2) in
      match x with
      | (l2, d2, r2) =>
        let! x := (merge_rec counter) f l1 l2 in
        let! x_1 := (merge_rec counter) f r1 r2 in
        concat_or_join x v1 (f v1 (Some d1) d2) x_1
      end
    | (_, Node l2 v2 d2 r2 h2) =>
      let! x := lift [_;_;_;_] "1110" (split v2 s1) in
      match x with
      | (l1, d1, r1) =>
        let! x := (merge_rec counter) f l1 l2 in
        let! x_1 := (merge_rec counter) f r1 r2 in
        concat_or_join x v2 (f v2 d1 (Some d2)) x_1
      end
    end
  end.

Definition merge {A B C : Type}
  (f : key -> (option A) -> (option B) -> option C) (s1 : t A) (s2 : t B)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] (t C) :=
  let! x := lift [_;_;_;_] "1000" (read_counter tt) in
  merge_rec x f s1 s2.

Fixpoint filter {A : Type} (p : key -> A -> bool) (x : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ] (t A) :=
  match x with
  | Empty => ret Empty
  | Node l v d r _ =>
    let! l' := filter p l in
    let pvd := p v d in
    let! r' := filter p r in
    if pvd then
      lift [_;_;_;_] "1110" (join l' v d r')
    else
      concat l' r'
  end.

Fixpoint partition {A : Type} (p : key -> A -> bool) (x : t A)
  : M [ Counter; NonTermination; OCaml.Invalid_argument; OCaml.Not_found ]
    ((t A) * (t A)) :=
  match x with
  | Empty => ret (Empty, Empty)
  | Node l v d r _ =>
    let! x_1 := partition p l in
    match x_1 with
    | (lt, lf) =>
      let pvd := p v d in
      let! x_1 := partition p r in
      match x_1 with
      | (rt, rf) =>
        if pvd then
          let! x_1 := lift [_;_;_;_] "1110" (join lt v d rt) in
          let! x_2 := concat lf rf in
          ret (x_1, x_2)
        else
          let! x_1 := concat lt rt in
          let! x_2 := lift [_;_;_;_] "1110" (join lf v d rf) in
          ret (x_1, x_2)
      end
    end
  end.

Inductive enumeration (a : Type) : Type :=
| End : enumeration a
| More : key -> a -> (t a) -> (enumeration a) -> enumeration a.
Arguments End {a}.
Arguments More {a} _ _ _ _.

Fixpoint cons_enum {A : Type} (m : t A) (e : enumeration A) : enumeration A :=
  match m with
  | Empty => e
  | Node l v d r _ => cons_enum l (More v d r e)
  end.

Definition compare {A B : Type} (cmp : A -> B -> Z) (m1 : t A) (m2 : t B)
  : M [ Counter; NonTermination ] Z :=
  let fix compare_aux_rec
    (counter : nat) (e1 : enumeration A) (e2 : enumeration B)
    : M [ NonTermination ] Z :=
    match counter with
    | O => not_terminated tt
    | S counter =>
      match (e1, e2) with
      | (End, End) => ret 0
      | (End, _) => ret (-1)
      | (_, End) => ret 1
      | (More v1 d1 r1 e1, More v2 d2 r2 e2) =>
        let c := Ord.compare v1 v2 in
        if nequiv_decb c 0 then
          ret c
        else
          let c := cmp d1 d2 in
          if nequiv_decb c 0 then
            ret c
          else
            (compare_aux_rec counter) (cons_enum r1 e1) (cons_enum r2 e2)
      end
    end in
  let compare_aux (e1 : enumeration A) (e2 : enumeration B)
    : M [ Counter; NonTermination ] Z :=
    let! x := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (compare_aux_rec x e1 e2) in
  compare_aux (cons_enum m1 End) (cons_enum m2 End).

Definition equal {A B : Type} (cmp : A -> B -> bool) (m1 : t A) (m2 : t B)
  : M [ Counter; NonTermination ] bool :=
  let fix equal_aux_rec
    (counter : nat) (e1 : enumeration A) (e2 : enumeration B)
    : M [ NonTermination ] bool :=
    match counter with
    | O => not_terminated tt
    | S counter =>
      match (e1, e2) with
      | (End, End) => ret true
      | (End, _) => ret false
      | (_, End) => ret false
      | (More v1 d1 r1 e1, More v2 d2 r2 e2) =>
        let! x :=
          let! x := (equal_aux_rec counter) (cons_enum r1 e1) (cons_enum r2 e2)
            in
          ret (andb (cmp d1 d2) x) in
        ret (andb (equiv_decb (Ord.compare v1 v2) 0) x)
      end
    end in
  let equal_aux (e1 : enumeration A) (e2 : enumeration B)
    : M [ Counter; NonTermination ] bool :=
    let! x := lift [_;_] "10" (read_counter tt) in
    lift [_;_] "01" (equal_aux_rec x e1 e2) in
  equal_aux (cons_enum m1 End) (cons_enum m2 End).

Fixpoint cardinal {A : Type} (x : t A) : Z :=
  match x with
  | Empty => 0
  | Node l _ _ r _ => Z.add (Z.add (cardinal l) 1) (cardinal r)
  end.

Fixpoint bindings_aux {A : Type} (accu : list (key * A)) (x : t A)
  : list (key * A) :=
  match x with
  | Empty => accu
  | Node l v d r _ => bindings_aux (cons (v, d) (bindings_aux accu r)) l
  end.

Definition bindings {A : Type} (s : t A) : list (key * A) := bindings_aux [] s.

Definition choose {A : Type} : (t A) -> M [ OCaml.Not_found ] (key * A) :=
  min_binding.
