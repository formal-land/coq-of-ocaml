(** Pervasives *)

(* Exceptions *)
let e_invalid _ = invalid_arg "error"
let e_failure _ = failwith "error"
let e_exit1 _ = raise Pervasives.Exit
let e_exit2 _ = raise Exit

(* Comparisons *)
let b_eq = 1 = 2
let b_neq = 1 <> 2
(* let b_lt = 1 < 2 *)
(* let b_gt = 1 > 2 *)
(* let b_le = 1 <= 2 *)
(* let b_ge = 1 >= 2 *)
(* let comp = compare 1 2 *)
(* let n_min = min 1 2 *)
(* let n_max = max 1 2 *)
(* let n_phys_eq = 1 == 2 *)
(* let n_phys_neq = 1 != 2 *)

(* Boolean operations *)
let b_not = not false
let b_and = true && false
let b_and_old = true & false
let b_or = true || false
let b_or_old = true or false

(* Composition operators *)
let app1 = 12 |> fun x -> x
let app2 = (fun x -> x) @@ 12

(* Integer arithmetic *)
let n_neg1 = ~- 12
let n_neg2 = - 12
let n_pos1 = ~+ 12
let n_pos2 = + 12
let n_succ = succ 1
let n_pred = pred 1
let n_plus = 1 + 2
let n_minus = 1 - 2
let n_times = 1 * 2
let n_div = 1 / 2
let n_mod = 1 mod 2
let n_abs = abs 1
(* let n_max = max_int *)
(* let n_min = min_int *)

(* Bitwise operations *)
let n_land = 12 land 13
let n_lor = 12 lor 13
let n_lxor = 12 lxor 13
(* let n_lnot = lnot 13 *)
let n_lsl = 12 lsl 13
let n_lsr = 12 lsr 13
(* let n_asr = 12 asr 13 *)

(* Floating-point arithmetic *)
(* String operations *)
(* Character operations *)
(* Unit operations *)
(* String conversion functions *)
(* Pair operations *)
(* List operations *)
(* Input/output *)
(* Output functions on standard output *)
(* Output functions on standard error *)
(* Input functions on standard input *)
(* General output functions *)
(* General input functions *)
(* Operations on large files *)
(* References *)
(* Operations on format strings *)
(* Program termination *)
let x = 2