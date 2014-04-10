(** Let rec and *)

let rec odd_length l =
  match l with
  | [] -> false
  | _ :: l -> not (even_length l)
  [@@coq_rec]

and even_length l =
  match l with
  | [] -> true
  | _ :: l -> not (odd_length l)

let rec odd_length_with_print l =
  match l with
  | [] -> print_endline "false"; false
  | _ :: l -> not (even_length_with_print l)
  [@@coq_rec]

and even_length_with_print l =
  match l with
  | [] -> true
  | _ :: l -> not (odd_length_with_print l)

let rec odd_length_free l =
  match l with
  | [] -> false
  | _ :: l -> not (even_length_free l)

and even_length_free l =
  match l with
  | [] -> true
  | _ :: l -> not (odd_length_free l)