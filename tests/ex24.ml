(** Pervasives *)

(* Exceptions *)
(* let e_raise e = raise e *)
let e_invalid _ = invalid_arg "error"
let e_failure _ = failwith "error"
let e_exit1 _ = raise Pervasives.Exit
let e_exit2 _ = raise Exit

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
(* TODO *)

(* String operations *)
let ss = "begin" ^ "end"

(* Character operations *)
let n_char = int_of_char 'c'
let char_n = char_of_int 23

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

(* Input/output *)
(* let input : in_channel = assert false *)
(* let output : out_channel = assert false *)
(* let std_channels = (stdin, stdout, stderr) *)

(* Output functions on standard output *)
let p_c _ = print_char 'c'
let p_s _ = print_string "str"
let p_n _ = print_int 12
(* let p_f _ = print_float 1.0 *)
let p_endline _ = print_endline "str"
let p_newline _ = print_newline ()

(* Output functions on standard error *)
let perr_c _ = prerr_char 'c'
let perr_s _ = prerr_string "str"
let perr_n _ = prerr_int 12
(* let perr_f _ = prerr_float 1.0 *)
let perr_endline _ = prerr_endline "str"
let perr_newline _ = prerr_newline ()

(* Input functions on standard input *)
let r_s _ = read_line ()
let r_n _ = read_int ()
(* let r_f _ = read_float () *)

(* General output functions *)
(* TODO *)
(* General input functions *)
(* TODO *)
(* Operations on large files *)
(* TODO *)
(* References *)
(* TODO *)
(* Operations on format strings *)
(* TODO *)
(* Program termination *)
(* TODO *)