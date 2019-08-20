(** GADTs *)

type 'a gre = Arg of 'a

type ('a , 'b) foo =
  | Bar : 'a * int * 'b * 'c -> ('b, string) foo
  | Other of int

type 'a expr =
  | Int : int expr
  | String : string expr
  | Sum : int expr * int expr -> int expr
  | Pair : 'a expr * 'b expr -> ('a * 'b) expr
