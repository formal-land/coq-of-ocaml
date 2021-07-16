module Wrapper = struct
  type tagged =
    | T1 : tagged
    | T2 : tagged
    | T3 : tagged

end

type 'a term =
  | T_Int : int -> int term
  | T_String : string -> string term
  | T_Sum : int term * int term -> int term
  | T_Wrap : Wrapper.tagged -> Wrapper.tagged term
[@@coq_tag_gadt]
