let head l =
  match l with
  | x :: _ -> x
  | [] -> failwith "Cannot take the head of an empty list."