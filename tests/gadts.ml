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

type 'a term =
  | T_Int : int -> int term
  | T_String : string -> string term
  | T_Sum : int expr * int expr -> int term
  | T_Pair : 'a expr * 'b expr -> ('a * 'b) term
[@@coq_tag_gadt]

let rec get_int (e : int term) : int =
  match[@coq_tagged_match][@coq_match_with_default] e with
  | T_Int n -> n
  | T_Sum (e1, e2) -> proj_int e1 + proj_int e2
  | _ -> .


type 'a one_case =
  | SingleCase : int one_case
  | Impossible : bool one_case

let x : int =
  match[@coq_match_with_default] SingleCase with
  | SingleCase -> 0

type[@coq_force_gadt] 'a gadt_list =
  | GNil
  | GCons of 'a * 'a gadt_list

let gadt_empty_list = GNil
