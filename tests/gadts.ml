type 'a gre = Arg of 'a

type ('a , 'b) foo =
  | Bar : 'a * int * 'b * 'c -> ('b, string) foo
  | Other of int

type 'a expr =
  | Int : int -> int expr
  | String : string -> string expr
  | Sum : int expr * int expr -> int expr
  | Pair : 'a expr * 'b expr -> ('a * 'b) expr

let rec proj_int (e : int expr) : int =
  match[@coq_match_with_default] e with
  | Int n -> n
  | Sum (e1, e2) -> proj_int e1 + proj_int e2
  | _ -> .

type 'a one_case =
  | SingleCase : int one_case
  | Impossible : bool one_case

let x : int =
  match[@coq_match_with_default] SingleCase with
  | SingleCase -> 0
