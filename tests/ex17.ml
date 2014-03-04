(** Exceptions. *)

exception TailLess

exception Wtf of int * string

let f x = raise TailLess

module G = struct
  let g x = raise (Wtf (x, "no"))
end

let rec h l =
  match l with
  | [] -> print_string "no tail"; raise TailLess
  | [x] -> x
  | _ :: xs -> h xs