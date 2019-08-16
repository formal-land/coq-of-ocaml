(** Some recursives functions *)

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
