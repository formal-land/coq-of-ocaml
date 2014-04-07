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