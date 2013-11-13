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

let incr x = x + 1

let n = fold (fun x y -> x + y) 0 (map incr l)
