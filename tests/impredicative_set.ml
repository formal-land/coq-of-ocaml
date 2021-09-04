type t =
  | Empty
  | Node : 'a -> t

let rec t_of_list (l : 'a list) : t =
  match l with
  | [] -> Empty
  | _ :: l -> Node (t_of_list l)
