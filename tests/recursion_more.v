Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Fixpoint f_map {A B : Set} (f_value : A -> B) (l_value : list A) : list B :=
  match l_value with
  | [] => nil
  | cons x_value l_value => cons (f_value x_value) (f_map f_value l_value)
  end.

Definition n_value : int :=
  let fix sum (l_value : list int) : int :=
    match l_value with
    | [] => 0
    | cons x_value l_value => Z.add x_value (sum l_value)
    end in
  sum [ 1; 2; 3 ].

Reserved Notation "'double".

Fixpoint double_list (l_value : list int) : list int :=
  let double := 'double in
  match l_value with
  | [] => l_value
  | cons n_value l_value => cons (double n_value) (double_list l_value)
  end

where "'double" := (fun (n_value : int) => Z.mul 2 n_value).

Definition double := 'double.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : list (tree a) -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Reserved Notation "'zero".
Reserved Notation "'sums".

Fixpoint sum (t_value : tree int) : int :=
  let zero := 'zero in
  let sums := 'sums in
  match t_value with
  | Leaf n_value => n_value
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
    | cons t_value ts => Z.add (sum t_value) (sums ts)
    end).

Definition zero := 'zero.
Definition sums := 'sums.

Reserved Notation "'counts".
Reserved Notation "'length".

Fixpoint count {A : Set} (t_value : tree (list A)) : int :=
  let counts {A} := 'counts A in
  let length {A} := 'length A in
  match t_value with
  | Leaf l_value => length l_value
  | Node ts => counts ts
  end

where "'counts" :=
  (fun (A : Set) => fix counts (ts : list (tree (list A))) {struct ts} : int :=
    match ts with
    | [] => 0
    | cons t_value ts => Z.add (count t_value) (counts ts)
    end)

and "'length" :=
  (fun (A : Set) => fun (l_value : list A) =>
    let counts {A} := 'counts A in
    CoqOfOCaml.List.length l_value).

Definition counts {A : Set} := 'counts A.
Definition length {A : Set} := 'length A.
