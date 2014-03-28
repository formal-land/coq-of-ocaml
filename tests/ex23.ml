(** The core library *)

(* Built-in types *)
let n = 12
let c1 = 'a'
let c2 = '\n'
let c3 = '\t'
let c4 = '"'
let s = "hi\n\t:)\""
(* let f = 1.0 *)
let b1 = false
let b2 = true
let u = ()
(* let x : exn = assert false *)
(* let a : bool array = assert false *)
let l1 = []
let l2 = 0 :: [1; 2; 3]
let o = if b1 then None else Some n
(* let n32 : int32 = assert false *)
(* let n64 : int64 = assert false *)
(* let n_native : nativeint = assert false *)
(* let form : (unit, unit, unit, unit, unit, unit) format6 = assert false *)
(* let laz : unit lazy_t = assert false *)

(* Predefined exceptions *)
let e_match _ = raise (Match_failure ("error", 1, 2))
let e_assert _ = raise (Assert_failure ("error", 1, 2))
let e_invalid _ = raise (Invalid_argument "error")
let e_failure _ = raise (Failure "error")
let e_not_found _ = raise Not_found
let e_out_of_mem _ = raise Out_of_memory
let e_overflow _ = raise Stack_overflow
let e_sys_err _ = raise (Sys_error "error")
let e_EOF _ = raise End_of_file
let e_div _ = raise Division_by_zero
let e_sys_blocked _ = raise Sys_blocked_io
let e_rec_module _ = raise (Undefined_recursive_module ("error", 1, 2))