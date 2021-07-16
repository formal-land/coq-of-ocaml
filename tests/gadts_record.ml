type 'a term =
  (* | T_Int : int -> int term *)
  (* | T_String : string -> string term *)
  | T_Pair : 'a term * 'b term -> ('a * 'b) term
  | T_Rec : { x : 'a term; y : 'b } -> ('a * 'b) term
[@@coq_tag_gadt]

let rec interp : type a. a term -> a = function
  (* | T_Int n -> n *)
  (* | T_String s -> s *)
  | T_Pair (p1, p2) -> (interp p1, interp p2)
  | T_Rec {x; y} -> (interp x, y)
