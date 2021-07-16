type _ exp =
  | E_Int : int -> int exp
[@@coq_tag_gadt]

type 'a term =
  | T_constr : {
      b : 'a exp
    } -> 'a term
[@@coq_tag_gadt]

type wrapper =
  (* | W_int : int -> wrapper *)
  | W_exp : { x : 'kind exp } -> wrapper
  | W_term : { x : 'kind term } -> wrapper

let unwrap w1 w2  =
  match (w1, w2) with
  | W_exp e1, W_term e2 -> 2
  | _ -> 4
