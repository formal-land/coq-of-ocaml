(** Function with effects returning function with effects *)

let f x =
  print_string "Hi";
  fun y -> failwith "Bye"

let r _ = f 1 2
