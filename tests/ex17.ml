(** Exceptions. *)

exception Outside

let f x = raise Outside

module G = struct
  exception Inside of int * string

  let g b =
    if b then
      raise (Inside (12, "no"))
    else
      raise Outside
end

let rec h l =
  match l with
  | [] -> print_string "no tail"; G.g false
  | [x] -> raise (G.Inside (0, "gg"))
  | _ :: xs -> h xs
