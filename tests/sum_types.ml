type t1 =
  | C1 of int
  | C2 of bool * int
  | C3

let n = C2 (false, 3)

let m = match n with
  | C2 (b, _) -> b
  | _ -> true

type 'a t2 =
  | D1
  | D2 of 'a * 'a t2

let rec of_list l =
  match l with
  | [] -> D1
  | x :: xs -> D2 (x, of_list xs)

let rec sum l =
  match l with
  | D1 -> 0
  | D2 (x, xs) -> x + sum xs

let s _ = sum (of_list [5; 7; 3])

type t3
type 'a t4
type t5 = C

type single_string = Single of string

let get_string s : string =
  let Single s = s in
  s
