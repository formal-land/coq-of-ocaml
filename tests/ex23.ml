(** The core library *)

(* Built-in types *)
let n = 12
let c1 = 'a'
let c2 = '\n'
let c3 = '\t'
let c4 = '"'
let s = "hi\n\t:)\""
let b1 = false
let b2 = true
let u = ()
let l1 = []
let l2 = 0 :: [1; 2; 3]
let o = if b1 then None else Some n

(* Predefined exceptions *)
let e_match _ = raise (Match_failure ("error", 1, 2))
let e_assert _ = raise (Assert_failure ("error", 1, 2))
let e_invalid _ = raise (Invalid_argument "error")
let e_failure _ = raise (Failure "error")
let e_not_found _ = raise Not_found
let e_EOF _ = raise End_of_file
let e_div _ = raise Division_by_zero