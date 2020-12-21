let rec f_map f l =
  match l with
  | [] -> []
  | x :: l -> f x :: f_map f l

let n =
  let rec sum l =
    match l with
    | [] -> 0
    | x :: l -> x + sum l in
  sum [1; 2; 3]

let rec double_list l =
  match l with
  | [] -> l
  | n :: l -> double n :: double_list l

and[@coq_mutual_as_notation] double n = 2 * n

type 'a tree =
  | Leaf of 'a
  | Node of 'a tree list

let rec sum (t : int tree) =
  match t with
  | Leaf n -> n
  | Node ts -> sums ts

and[@coq_mutual_as_notation] zero () = 0

and[@coq_mutual_as_notation][@coq_struct "ts"] sums (ts : int tree list) =
  match ts with
  | [] -> zero ()
  | t :: ts -> sum t + sums ts

(* Notation with polymorphism *)
let rec count t =
  match t with
  | Leaf l -> length l
  | Node ts -> counts ts

and[@coq_mutual_as_notation][@coq_struct "ts"] counts ts =
  match ts with
  | [] -> 0
  | t :: ts -> count t + counts ts

and[@coq_mutual_as_notation] length l =
  List.length l
