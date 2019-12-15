module List2 = struct
  type 'a t =
    | Nil
    | Cons of 'a * 'a t

  let rec sum (l : int t) : int =
    match l with
    | Nil -> 0
    | Cons (x, xs) -> x + sum xs

  let rec of_list = function
    | [] -> Nil
    | x :: xs -> Cons (x, of_list xs)

  module Inside = struct
    let x = 12
  end
end

let n _ = List2.sum (List2.of_list [5; 7; 6; List2.Inside.x])

module Syn = List2.Inside

let xx = Syn.x

include Syn

let y = x
