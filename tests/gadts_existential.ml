type 'a term =
  | T_Int : int -> int term
  | T_String : string -> string term
  (* | T_Sum : int term * int term -> int term *)
  (* | T_Pair : 'a term * 'b term -> ('a * 'b) term *)
(* [@@coq_tag_gadt] *)

type 'kind operation_metadata = {contents : 'kind term}

type operation =
  | Op : 'kind operation_metadata -> operation
  | Op1 : operation

(* let unpack (op : operation) : int =
 *     match op with
 *     | Op {contents} -> 2
 *     | Op1 -> 5 *)

let unpack1 (op : operation) : int =
    match op with
    | Op oop -> 2
    | Op1 -> 5
