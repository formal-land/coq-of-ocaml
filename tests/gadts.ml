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
  | T_Sum : int term * int term -> int term
  (* | T_Pair : 'a term * 'b term -> ('a * 'b) term *)
[@@coq_tag_gadt]

let rec get_int (e : int term) : int =
  match[@coq_tagged_match][@coq_match_with_default] e with
  | T_Int n -> n
  | T_Sum (e1, e2) -> get_int e1 + get_int e2
  | _ -> .

let rec interp : type a. a term -> a = function
  | T_Int n -> n
  | T_String s -> s
  | T_Sum (s1, s2) -> interp s1 + interp s2


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

module With_cast = struct
  type 'a int_or_bool =
    | Int : int int_or_bool
    | Bool : bool int_or_bool

  let to_int (type a) (kind : a int_or_bool) (x : a) : int =
    match[@coq_match_gadt] (kind, x) with
    | (Int, (x : int)) -> x
    | (Bool, (x : bool)) -> if x then 1 else 0
end
