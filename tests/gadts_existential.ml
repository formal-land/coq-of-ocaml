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

type _ ty =
  | Ty_bool : bool ty
  | Ty_pair : 'a ty * 'b ty -> ('a * 'b) ty

let rec match_with_used_unused_existentials :
  type a. int list -> a ty -> (a -> a) -> int =
  fun fuel t _ ->
  match fuel with
  | [] -> 0
  | _ :: l ->
    match[@coq_match_gadt] t with
    | Ty_bool -> 12
    | Ty_pair (t1, t2) -> match_with_used_unused_existentials l t1 (fun x -> x)
