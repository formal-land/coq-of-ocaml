(** The initially opened module. *)
open FullEnvi
open SmartPrint

let env_with_effects : unit FullEnvi.t =
  FullEnvi.empty (fun _ _ -> ())
  (* Values specific to the translation to Coq *)
  |> add_typ [] "nat"
  |> add_constructor [] "O"
  |> add_constructor [] "S"
  |> add_typ [] "sum"
  |> add_constructor [] "inl"
  |> add_constructor [] "inr"
  |> add_var [] "read_counter" ()
  |> add_var [] "not_terminated" ()
  |> add_var ["OCaml"] "assert" ()

  (* The core library *)
  (* Built-in types *)
  |> add_typ [] "Z"
  |> add_typ [] "ascii"
  |> add_typ [] "string"
  |> add_typ [] "bool"
  |> add_constructor [] "false"
  |> add_constructor [] "true"
  |> add_typ [] "unit"
  |> add_constructor [] "tt"
  |> add_typ [] "list"
  |> add_constructor [] "[]"
  |> add_constructor [] "cons"
  |> add_typ [] "option"
  |> add_constructor [] "None"
  |> add_constructor [] "Some"

  (* Pervasives *)
  (* Comparisons *)
  |> add_var [] "equiv_decb" ()
  |> add_var [] "nequiv_decb" ()
  |> add_var ["OCaml"; "Pervasives"] "lt" ()
  |> add_var ["OCaml"; "Pervasives"] "gt" ()
  |> add_var ["OCaml"; "Pervasives"] "le" ()
  |> add_var ["OCaml"; "Pervasives"] "ge" ()
  |> add_var ["OCaml"; "Pervasives"] "compare" ()
  |> add_var ["OCaml"; "Pervasives"] "min" ()
  |> add_var ["OCaml"; "Pervasives"] "max" ()
  (* Boolean operations *)
  |> add_var [] "negb" ()
  |> add_var [] "andb" ()
  |> add_var [] "orb" ()
  (* Composition operators *)
  |> add_var ["OCaml"; "Pervasives"] "reverse_apply" ()
  |> add_var [] "apply" ()
  (* Integer arithmetic *)
  |> add_var ["Z"] "opp" ()
  |> add_var [] "" ()
  |> add_var ["Z"] "succ" ()
  |> add_var ["Z"] "pred" ()
  |> add_var ["Z"] "add" ()
  |> add_var ["Z"] "sub" ()
  |> add_var ["Z"] "mul" ()
  |> add_var ["Z"] "div" ()
  |> add_var ["Z"] "modulo" ()
  |> add_var ["Z"] "abs" ()
  (* Bitwise operations *)
  |> add_var ["Z"] "land" ()
  |> add_var ["Z"] "lor" ()
  |> add_var ["Z"] "lxor" ()
  |> add_var ["Z"] "shiftl" ()
  |> add_var ["Z"] "shiftr" ()
  (* Floating-point arithmetic *)
  (* String operations *)
  |> add_var ["String"] "append" ()
  (* Character operations *)
  |> add_var ["OCaml"; "Pervasives"] "int_of_char" ()
  |> add_var ["OCaml"; "Pervasives"] "char_of_int" ()
  (* Unit operations *)
  |> add_var ["OCaml"; "Pervasives"] "ignore" ()
  (* String conversion functions *)
  |> add_var ["OCaml"; "Pervasives"] "string_of_bool" ()
  |> add_var ["OCaml"; "Pervasives"] "bool_of_string" ()
  |> add_var ["OCaml"; "Pervasives"] "string_of_int" ()
  |> add_var ["OCaml"; "Pervasives"] "int_of_string" ()
  (* Pair operations *)
  |> add_var [] "fst" ()
  |> add_var [] "snd" ()
  (* List operations *)
  |> add_var ["OCaml"; "Pervasives"] "app" ()
  (* Input/output *)
  (* Output functions on standard output *)
  |> add_var ["OCaml"; "Pervasives"] "print_char" ()
  |> add_var ["OCaml"; "Pervasives"] "print_string" ()
  |> add_var ["OCaml"; "Pervasives"] "print_int" ()
  |> add_var ["OCaml"; "Pervasives"] "print_endline" ()
  |> add_var ["OCaml"; "Pervasives"] "print_newline" ()
  (* Output functions on standard error *)
  |> add_var ["OCaml"; "Pervasives"] "prerr_char" ()
  |> add_var ["OCaml"; "Pervasives"] "prerr_string" ()
  |> add_var ["OCaml"; "Pervasives"] "prerr_int" ()
  |> add_var ["OCaml"; "Pervasives"] "prerr_endline" ()
  |> add_var ["OCaml"; "Pervasives"] "prerr_newline" ()
  (* Input functions on standard input *)
  |> add_var ["OCaml"; "Pervasives"] "read_line" ()
  |> add_var ["OCaml"; "Pervasives"] "read_int" ()
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Operations on format strings *)
  (* Program termination *)

  |> enter_module
  |> open_module ["OCaml"]
  (* |> fun env -> SmartPrint.to_stdout 80 2 (FullEnvi.pp env); env *)

let env : unit FullEnvi.t =
  { env_with_effects with
    vars = Envi.map env_with_effects.vars (fun _ -> ());
    leave_prefix_vars = (fun _ () -> ()) }
