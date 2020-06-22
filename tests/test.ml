type _ foo =
  | FooC : bar -> bar foo
  | FooC2 : 'a -> 'a foo
and
  bar =
  | BarC

(*
type ('a , 'b) foo =
  | Bar : 'a * int * 'b * 'c -> ('b, string) foo
  | Other of int

Translation we want:
Inductive pre_foo : Set :=
| Bar : forall {a b c : Set}, a -> int -> b -> c -> foo
| Other : int -> foo.

Fixpoint foo_wf (t : foo) (a : Set) (b : Set) :=
   match t with
   | Bar _ _ _ _ => (a = unit) /\ (b = string)
   | Other => (a = unit) /\ (b = unit)

type 'a expr =
  | Int : int -> int expr
  | String : string -> string expr
  | Sum : int expr * int expr -> int expr
  | Pair : 'a expr * 'b expr -> ('a * 'b) expr

let rec proj_int (e : int expr) : int =
  match[@coq_match_with_default] e with
  | Int n -> n
  | Sum (e1, e2) -> proj_int e1 + proj_int e2

type 'a one_case =
  | SingleCase : int one_case
  | Impossible : bool one_case

let x : int =
  match[@coq_match_with_default] SingleCase with
  | SingleCase -> 0
*)
