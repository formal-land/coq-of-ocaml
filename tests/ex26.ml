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

let n =
  let rec sum l =
    match l with
    | [] -> 0
    | x :: l -> x + sum l
  [@@coq_rec] in
  sum [1; 2; 3]

let n2 _ =
  let rec sum l =
    match l with
    | [] -> 0
    | x :: l -> x + sum l
  [@@free_rec] in
  sum [1; 2; 3]