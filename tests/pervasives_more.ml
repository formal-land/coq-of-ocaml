(* Comparisons *)
let b_eq = 1 = 2
let b_neq1 = true <> false
let b_neq2 = () <> ()
let b_lt = 1 < 2
let b_gt = 1 > 2
let b_le = true <= false
let b_ge = () >= ()
let comp = compare 1 2
let n_min = min 1 2
let n_max = max 1 2
(* let n_phys_eq = 1 == 2 *)
(* let n_phys_neq = 1 != 2 *)

(* Boolean operations *)
let b_not = not false
let b_and = true && false
(* let b_and_old = true & false *)
let b_or = true || false
(* let b_or_old = true or false *)

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
(* TODO *)

(* String operations *)
let ss = "begin" ^ "end"

(* Character operations *)
let n_char = int_of_char 'c'

(* Unit operations *)
let i = ignore 12

(* String conversion functions *)
let s_bool = string_of_bool false
let bool_s = bool_of_string "false"
let s_n = string_of_int 12
let n_s = int_of_string "12"
(* let s_f = string_of_float 1.0 *)
(* let f_s = float_of_string "1.0" *)

(* Pair operations *)
let n1 = fst (12, 13)
let n2 = snd (12, 13)

(* List operations *)
let ll = [1; 2] @ [3; 4]

(* Operations on format strings *)
(* TODO *)
