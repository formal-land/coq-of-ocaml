let map f l =
  let rec map_coq_rec l =
    match l with
    | [] -> []
    | x :: l -> f x :: map_coq_rec l in
  map_coq_rec l

let map2 f l =
  let rec map2_coq_rec f l =
    match l with
    | [] -> []
    | x :: l -> f x :: map2_coq_rec f l in
  map2_coq_rec f l
