let return (x : 'a) : 'a option =
  Some x

let (let*) (x : 'a option) (f : 'a -> 'b option) : 'b option =
  match [@coq_disable_existential] x with
  | Some x -> f x
  | None -> None

let get_head l =
  match l with
  | [] -> None
  | x :: _ -> Some x

let insert_monadic_notations_here = ()

let sum_first_elements l1 l2 =
  let* x1 = get_head l1 in
  let* (x2, x3) = get_head l2 in
  return (x1 + x2 + x3)
