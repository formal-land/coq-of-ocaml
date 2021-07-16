type _ exp =
  | E_Int : int -> int exp
[@@coq_tag_gadt]

type 'a term =
  | T_constr : {
      b : 'a exp
    } -> 'a term
[@@coq_tag_gadt]
