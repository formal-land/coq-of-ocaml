(** Recursion *)

let rec map f l =
  match l with
  | [] -> []
  | x :: xs -> f x :: map f xs

let rec fold f a l =
  match l with
  | [] -> a
  | x :: xs -> fold f (f a x) xs

let l = [5; 6; 7; 2]

let n incr plus =
  fold (fun x y -> plus x y) 0 (map incr l)
