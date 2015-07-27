(** Local let-rec *)

let l _ =
  let rec map f = function
    | [] -> []
    | x :: xs -> f x :: map f xs in
  let rec loop x = x in
  map (fun n -> n + 1) [5; 7; 8]
