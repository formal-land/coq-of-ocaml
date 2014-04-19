(** The initially opened module. *)
open FullEnvi
open Effect.Type
open Envi.Visibility
open SmartPrint

let env_with_effects : Effect.Type.t FullEnvi.t =
  let descriptor (path, base) =
    let x = PathName.of_name path base in
    Effect.Descriptor.singleton (Loc.Ether x)
      { BoundName.path_name = x; depth = 0 } in
  let d xs : Effect.Descriptor.t =
    Effect.Descriptor.union (List.map descriptor xs) in
  let add_exn path base =
    add_exception_with_effects path base
      (Loc.Ether (PathName.of_name path base)) in
  FullEnvi.empty Effect.Type.leave_prefix
  (* Values specific to the translation to Coq *)
  |> add_typ [] "nat" Global
  |> add_constructor [] "O" Global
  |> add_constructor [] "S" Global
  |> add_typ [] "sum" Global
  |> add_constructor [] "inl" Global
  |> add_constructor [] "inr" Global
  |> add_descriptor [] "IO" Global
  |> add_descriptor [] "Counter" Global
  |> add_var [] "read_counter" Global (Arrow (d [[], "Counter"], Pure))
  |> add_descriptor [] "NonTermination" Global
  |> add_var [] "not_terminated" Global (Arrow (d [[], "NonTermination"], Pure))
  |> add_var ["OCaml"] "assert" Global (Arrow (d [["OCaml"], "Assert_failure"], Pure))

  (* The core library *)
  (* Built-in types *)
  |> add_typ [] "Z" Global
  |> add_typ [] "ascii" Global
  |> add_typ [] "string" Global
  |> add_typ [] "bool" Global
  |> add_constructor [] "false" Global
  |> add_constructor [] "true" Global
  |> add_typ [] "unit" Global
  |> add_constructor [] "tt" Global
  |> add_typ [] "list" Global
  |> add_constructor [] "[]" Global
  |> add_constructor [] "cons" Global
  |> add_typ [] "option" Global
  |> add_constructor [] "None" Global
  |> add_constructor [] "Some" Global
  (* Predefined exceptions *)
  |> add_exn ["OCaml"] "Match_failure" Global
  |> add_exn ["OCaml"] "Assert_failure" Global
  |> add_exn ["OCaml"] "Invalid_argument" Global
  |> add_exn ["OCaml"] "Failure" Global
  |> add_exn ["OCaml"] "Not_found" Global
  |> add_exn ["OCaml"] "Out_of_memory" Global
  |> add_exn ["OCaml"] "Stack_overflow" Global
  |> add_exn ["OCaml"] "Sys_error" Global
  |> add_exn ["OCaml"] "End_of_file" Global
  |> add_exn ["OCaml"] "Division_by_zero" Global
  |> add_exn ["OCaml"] "Sys_blocked_io" Global
  |> add_exn ["OCaml"] "Undefined_recursive_module" Global

  (* Pervasives *)
  (* Exceptions *)
  |> add_var ["OCaml"; "Pervasives"] "invalid_arg" Global (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "failwith" Global (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_exn ["OCaml"; "Pervasives"] "Exit" Global
  (* Comparisons *)
  |> add_var [] "equiv_decb" Global Pure
  |> add_var [] "nequiv_decb" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "lt" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "gt" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "le" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "ge" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "compare" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "min" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "max" Global Pure
  (* Boolean operations *)
  |> add_var [] "negb" Global Pure
  |> add_var [] "andb" Global Pure
  |> add_var [] "orb" Global Pure
  (* Composition operators *)
  |> add_var ["OCaml"; "Pervasives"] "reverse_apply" Global Pure
  |> add_var [] "apply" Global Pure
  (* Integer arithmetic *)
  |> add_var ["Z"] "opp" Global Pure
  |> add_var [] "" Global Pure
  |> add_var ["Z"] "succ" Global Pure
  |> add_var ["Z"] "pred" Global Pure
  |> add_var ["Z"] "add" Global Pure
  |> add_var ["Z"] "sub" Global Pure
  |> add_var ["Z"] "mul" Global Pure
  |> add_var ["Z"] "div" Global Pure
  |> add_var ["Z"] "modulo" Global Pure
  |> add_var ["Z"] "abs" Global Pure
  (* Bitwise operations *)
  |> add_var ["Z"] "land" Global Pure
  |> add_var ["Z"] "lor" Global Pure
  |> add_var ["Z"] "lxor" Global Pure
  |> add_var ["Z"] "shiftl" Global Pure
  |> add_var ["Z"] "shiftr" Global Pure
  (* Floating-point arithmetic *)
  (* String operations *)
  |> add_var ["String"] "append" Global Pure
  (* Character operations *)
  |> add_var ["OCaml"; "Pervasives"] "int_of_char" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "char_of_int" Global Pure
  (* Unit operations *)
  |> add_var ["OCaml"; "Pervasives"] "ignore" Global Pure
  (* String conversion functions *)
  |> add_var ["OCaml"; "Pervasives"] "string_of_bool" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "bool_of_string" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "string_of_int" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "int_of_string" Global Pure
  (* Pair operations *)
  |> add_var [] "fst" Global Pure
  |> add_var [] "snd" Global Pure
  (* List operations *)
  |> add_var ["OCaml"; "Pervasives"] "app" Global Pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> add_var ["OCaml"; "Pervasives"] "print_char" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_string" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_int" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_endline" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_newline" Global (Arrow (d [[], "IO"], Pure))
  (* Output functions on standard error *)
  |> add_var ["OCaml"; "Pervasives"] "prerr_char" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_string" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_int" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_endline" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_newline" Global (Arrow (d [[], "IO"], Pure))
  (* Input functions on standard input *)
  |> add_var ["OCaml"; "Pervasives"] "read_line" Global (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "read_int" Global (Arrow (d [[], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  |> enter_module
  |> Interface.to_full_envi (Interface.of_file "interfaces/list.interface")
  |> leave_module "OCaml"
  |> enter_module
  |> open_module ["OCaml"]
  (* |> fun env -> SmartPrint.to_stdout 80 2 (FullEnvi.pp env); env *)

let env : unit FullEnvi.t =
  { env_with_effects with
    vars = Envi.map env_with_effects.vars (fun _ -> ());
    leave_prefix_vars = (fun _ () -> ()) }