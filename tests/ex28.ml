(** Free type variables *)

let map f l =
  let rec map l =
    match l with
    | [] -> []
    | x :: l -> f x :: map l in
  map l

let map2 f l =
  let rec map2 f l =
    match l with
    | [] -> []
    | x :: l -> f x :: map2 f l in
  map2 f l