(** Effects *)

let tail l =
  match l with
  | _ :: xs -> xs
  | [] -> failwith "Cannot take the tail of an empty list."

let rec print_list = function
  | [] -> ()
  | x :: xs ->
    print_int x;
    print_list xs

let f = print_list

let x z = f (tail [5; 7; 8])