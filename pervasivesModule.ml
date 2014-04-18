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
  |> Interface.to_full_envi (Interface.of_file "list.interface")
  |> leave_module "OCaml"
  (* |> fun env -> SmartPrint.to_stdout 80 2 (FullEnvi.pp env); env *)
  (*|> add_var ["OCaml"; "List"] "length" Global Pure
  |> add_var ["OCaml"; "List"] "hd" Global (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_var ["OCaml"; "List"] "tl" Global (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_var ["OCaml"; "List"] "nth" Global (Arrow (d [], Arrow (d [["OCaml"], "Failure"; ["OCaml"], "Invalid_argument"], Pure)))
  |> add_var ["List"] "rev" Global Pure
  |> add_var ["OCaml"; "Pervasives"] "app" Global Pure
  |> add_var ["List"] "rev_append" Global Pure
  |> add_var ["OCaml"; "List"] "flatten" Global Pure
  (* Iterators *)
  |> add_var ["List"] "map" Global Pure
  |> add_var ["OCaml"; "List"] "mapi" Global Pure
  |> add_var ["OCaml"; "List"] "rev_map" Global Pure
  |> add_var ["OCaml"; "List"] "fold_left" Global Pure
  |> add_var ["OCaml"; "List"] "fold_right" Global Pure
  (* Iterators on two lists *)
  |> add_var ["OCaml"; "List"] "map2" Global (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))
  |> add_var ["OCaml"; "List"] "rev_map2" Global (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))
  |> add_var ["OCaml"; "List"] "fold_left2" Global (Arrow (d [], (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))))
  |> add_var ["OCaml"; "List"] "fold_right2" Global (Arrow (d [], (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))))
  (* List scanning *)
  |> add_var ["List"] "forallb" Global Pure
  |> add_var ["List"] "existsb" Global Pure
  |> add_var ["OCaml"; "List"] "for_all2" Global (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "List"] "exists2" Global (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "List"] "mem" Global Pure
  (* List searching *)
  |> add_var ["OCaml"; "List"] "find" Global Pure
  |> add_var ["List"] "filter" Global Pure
  |> add_var ["List"] "partition" Global Pure
  (* Association lists *)
  (* Lists of pairs *)
  (* Sorting *)*)
  |> open_module ["OCaml"]
  (* |> enter_module *)

(*let env_typs : unit Envi.t =
  Envi.open_module @@
  List.fold_left (fun env_typs (path, base) ->
    Envi.add (PathName.of_name path base) () env_typs)
    Envi.empty
    [ [], "unit";
      [], "bool";
      [], "nat";
      [], "Z";
      [], "ascii";
      [], "string";
      [], "option";
      [], "sum";
      [], "list" ]

let env_descriptors : unit Envi.t =
  Envi.open_module @@
  List.fold_left (fun env_descriptors (path, base) ->
    Envi.add (PathName.of_name path base) () env_descriptors)
    Envi.empty
    [ [], "IO";
      [], "Counter";
      [], "NonTermination";
      ["OCaml"], "Match_failure";
      ["OCaml"], "Assert_failure";
      ["OCaml"], "Invalid_argument";
      ["OCaml"], "Failure";
      ["OCaml"], "Not_found";
      ["OCaml"], "End_of_file";
      ["OCaml"], "Division_by_zero" ]

let env_constructors : unit Envi.t =
  Envi.open_module @@
  List.fold_left (fun env_constructors (path, base) ->
    Envi.add (PathName.of_name path base) () env_constructors)
    Envi.empty
    [ [], "tt";
      [], "false";
      [], "true";
      [], "O";
      [], "S";
      [], "None";
      [], "Some";
      [], "inl";
      [], "inr";
      [], "[]";
      [], "cons" ]

let env_fields : unit Envi.t =
  Envi.open_module Envi.empty

let env_effects : Effect.Type.t Envi.t =
  let d path base =
    let x = PathName.of_name path base in
    Effect.Descriptor.singleton (Loc.Ether x)
      { BoundName.path_name = x; depth = 0 } in
  Envi.open_module @@
  List.fold_left (fun env_effects (path, base, typ) ->
    Envi.add (PathName.of_name path base) typ env_effects)
    Envi.empty
    [ [], "equiv_decb", Pure;
      [], "nequiv_decb", Pure;
      ["Z"], "leb", Pure;
      ["Z"], "geb", Pure;
      ["Z"], "ltb", Pure;
      ["Z"], "gtb", Pure;
      [], "negb", Pure;
      [], "andb", Pure;
      [], "orb", Pure;
      [], "reverse_apply", Pure;
      [], "apply", Pure;
      ["Z"], "opp", Pure;
      [], "", Pure;
      ["Z"], "succ", Pure;
      ["Z"], "pred", Pure;
      ["Z"], "add", Pure;
      ["Z"], "sub", Pure;
      ["Z"], "mul", Pure;
      ["Z"], "div", Pure;
      ["Z"], "modulo", Pure;
      ["Z"], "abs", Pure;
      ["Z"], "land", Pure;
      ["Z"], "lor", Pure;
      ["Z"], "lxor", Pure;
      ["Z"], "shiftl", Pure;
      ["Z"], "shiftr", Pure;
      ["String"], "append", Pure;
      ["OCaml"; "Pervasives"], "int_of_char", Pure;
      ["OCaml"; "Pervasives"], "char_of_int", Pure;
      ["OCaml"; "Pervasives"], "ignore", Pure;
      [], "fst", Pure;
      [], "snd", Pure;
      ["OCaml"; "List"], "app", Pure;
      ["OCaml"; "Pervasives"], "invalid_arg", Arrow (d ["OCaml"] "Invalid_argument", Pure);
      ["OCaml"; "Pervasives"], "failwith", Arrow (d ["OCaml"] "Failure", Pure);
      ["OCaml"; "Pervasives"], "print_char", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "print_string", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "print_int", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "print_endline", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "print_newline", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "prerr_char", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "prerr_string", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "prerr_int", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "prerr_endline", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "prerr_newline", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "read_line", Arrow (d [] "IO", Pure);
      ["OCaml"; "Pervasives"], "read_int", Arrow (d [] "IO", Pure);
      [], "read_counter", Arrow (d [] "Counter", Pure);
      [], "not_terminated", Arrow (d [] "NonTermination", Pure);
      ["List"], "fold_left", Pure;
      ["List"], "fold_right", Pure;
      ["List"], "map", Pure;
      ["Pervasives"], "string_of_bool", Pure;
      ["Pervasives"], "string_of_int", Pure;
      ["String"], "get", Pure;
      ["String"], "escaped", Pure;
      ["String"], "length", Pure;
      ["String"], "make", Pure;
      ["String"], "sub", Pure ]

let env_with_effects : Effect.Type.t FullEnvi.t = {
  FullEnvi.vars = env_effects;
  close_lift_vars = Effect.Type.close_lift;
  typs = env_typs;
  descriptors = env_descriptors;
  constructors = env_constructors;
  fields = env_fields
}*)

let env : unit FullEnvi.t =
  { env_with_effects with
    vars = Envi.map env_with_effects.vars (fun _ -> ());
    leave_prefix_vars = (fun _ () -> ()) }