(** Exceptions. *)

exception TailLess

exception Wtf of int * string

let f x = raise TailLess

let g x = raise (Wtf (12, "no"))

let rec h l =
  match l with
  | [] -> print_string "no tail"; raise TailLess
  | [x] -> x
  | _ :: xs -> h xs