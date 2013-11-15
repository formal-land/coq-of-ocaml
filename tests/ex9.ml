(** Local let-rec *)
let l =
  let rec map f = function
    | [] -> []
    | x :: xs -> f x :: map f xs in
  map (fun n -> n + 1) [5; 7; 8]