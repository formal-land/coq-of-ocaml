module Test = struct
  type 'a term =
    | T_Pair : { x1: int; x2: 'a; x3 : 'b} -> ('a * 'b) term
  [@@coq_tag_gadt]
end

let rec interp (type a) (t : a Test.term) : int=
  match t with
  | T_Pair {x1; x2; x3} -> x1
