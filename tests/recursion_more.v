Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Fixpoint f_map {A B : Set} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => nil
  | cons x l => cons (f x) (f_map f l)
  end.

Definition n : int :=
  let fix sum (l : list int) : int :=
    match l with
    | [] => 0
    | cons x l => Z.add x (sum l)
    end in
  sum [ 1; 2; 3 ].

Reserved Notation "'double".

Fixpoint double_list (l : list int) : list int :=
  let double := 'double in
  match l with
  | [] => l
  | cons n l => cons (double n) (double_list l)
  end

where "'double" := (fun (n : int) => Z.mul 2 n).

Definition double := 'double.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : list (tree a) -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Reserved Notation "'zero".
Reserved Notation "'sums".

Fixpoint sum (t : tree int) : int :=
  let zero := 'zero in
  let sums := 'sums in
  match t with
  | Leaf n => n
  | Node ts => sums ts
  end

where "'zero" :=
  (fun (function_parameter : unit) =>
    let '_ := function_parameter in
    0)

and "'sums" :=
  (fix sums (ts : list (tree int)) {struct ts} : int :=
    let zero := 'zero in
    match ts with
    | [] => zero tt
    | cons t ts => Z.add (sum t) (sums ts)
    end).

Definition zero := 'zero.
Definition sums := 'sums.

Reserved Notation "'counts".
Reserved Notation "'length".

Fixpoint count {A : Set} (t : tree (list A)) : int :=
  let counts {A} := 'counts A in
  let length {A} := 'length A in
  match t with
  | Leaf l => length l
  | Node ts => counts ts
  end

where "'counts" :=
  (fun (A : Set) => fix counts (ts : list (tree (list A))) {struct ts} : int :=
    match ts with
    | [] => 0
    | cons t ts => Z.add (count t) (counts ts)
    end)

and "'length" :=
  (fun (A : Set) => fun (l : list A) =>
    let counts {A} := 'counts A in
    CoqOfOCaml.List.length l).

Definition counts {A : Set} := 'counts A.
Definition length {A : Set} := 'length A.
