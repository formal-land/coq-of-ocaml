let rec odd_length l =
  match l with
  | [] -> false
  | _ :: l -> not (even_length l)

and even_length l =
  match l with
  | [] -> true
  | _ :: l -> not (odd_length l)

let local_let_and_variables x =
  let y = 12 and z = 2 * x in
  y + z
