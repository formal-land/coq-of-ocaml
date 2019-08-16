(** Let rec and *)

let rec odd_length l =
  match l with
  | [] -> false
  | _ :: l -> not (even_length l)

and even_length l =
  match l with
  | [] -> true
  | _ :: l -> not (odd_length l)
