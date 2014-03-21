(** Try-with *)

exception Error

let x1 =
  try raise Error with
  | Error -> 12

let x2 _ =
  try raise Error with
  | Error -> failwith "arg"

let x3 b =
  try (if b then failwith "arg" else raise Error) with
  | Error -> 12