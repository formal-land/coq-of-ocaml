(** Annotation for recursives functions *)

let rec f_map f l =
  match l with
  | [] -> []
  | x :: l -> f x :: f_map f l
[@@coq_rec]

let rec f_map2 f l =
  match l with
  | [] -> []
  | x :: l -> f x :: f_map2 f l
[@@free_rec]

(* TODO: support coq recursion attribute inside lets *)
(*let n =
  let rec sum_coq_rec l =
    match l with
    | [] -> 0
    | x :: l -> x + sum_coq_rec l in
  sum_coq_rec [1; 2; 3]*)

let n2 _ =
  let rec sum l =
    match l with
    | [] -> 0
    | x :: l -> x + sum l in
  sum [1; 2; 3]