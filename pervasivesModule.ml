(** The initially opened module. *)
open FullEnvi
open Effect.Type
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
  FullEnvi.empty Effect.Type.close_lift
  (* Values specific to the translation to Coq *)
  |> add_typ [] "nat"
  |> add_constructor [] "O"
  |> add_constructor [] "S"
  |> add_typ [] "sum"
  |> add_constructor [] "inl"
  |> add_constructor [] "inr"
  |> add_descriptor [] "IO"
  |> add_descriptor [] "Counter"
  |> add_var [] "read_counter" (Arrow (d [[], "Counter"], Pure))
  |> add_descriptor [] "NonTermination"
  |> add_var [] "not_terminated" (Arrow (d [[], "NonTermination"], Pure))
  |> add_var ["OCaml"] "assert" (Arrow (d [["OCaml"], "Assert_failure"], Pure))

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
  (* Predefined exceptions *)
  |> add_exn ["OCaml"] "Match_failure"
  |> add_exn ["OCaml"] "Assert_failure"
  |> add_exn ["OCaml"] "Invalid_argument"
  |> add_exn ["OCaml"] "Failure"
  |> add_exn ["OCaml"] "Not_found"
  |> add_exn ["OCaml"] "Out_of_memory"
  |> add_exn ["OCaml"] "Stack_overflow"
  |> add_exn ["OCaml"] "Sys_error"
  |> add_exn ["OCaml"] "End_of_file"
  |> add_exn ["OCaml"] "Division_by_zero"
  |> add_exn ["OCaml"] "Sys_blocked_io"
  |> add_exn ["OCaml"] "Undefined_recursive_module"

  (* Pervasives *)
  (* Exceptions *)
  |> add_var ["OCaml"; "Pervasives"] "invalid_arg" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "failwith" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_exn ["OCaml"; "Pervasives"] "Exit"
  |> open_module
  (* Comparisons *)
  |> add_var [] "equiv_decb" Pure
  |> add_var [] "nequiv_decb" Pure
  |> add_var ["OCaml"; "Pervasives"] "lt" Pure
  |> add_var ["OCaml"; "Pervasives"] "gt" Pure
  |> add_var ["OCaml"; "Pervasives"] "le" Pure
  |> add_var ["OCaml"; "Pervasives"] "ge" Pure
  |> add_var ["OCaml"; "Pervasives"] "compare" Pure
  |> add_var ["OCaml"; "Pervasives"] "min" Pure
  |> add_var ["OCaml"; "Pervasives"] "max" Pure
  (* Boolean operations *)
  |> add_var [] "negb" Pure
  |> add_var [] "andb" Pure
  |> add_var [] "orb" Pure
  (* Composition operators *)
  |> add_var ["OCaml"; "Pervasives"] "reverse_apply" Pure
  |> add_var [] "apply" Pure
  (* Integer arithmetic *)
  |> add_var ["Z"] "opp" Pure
  |> add_var [] "" Pure
  |> add_var ["Z"] "succ" Pure
  |> add_var ["Z"] "pred" Pure
  |> add_var ["Z"] "add" Pure
  |> add_var ["Z"] "sub" Pure
  |> add_var ["Z"] "mul" Pure
  |> add_var ["Z"] "div" Pure
  |> add_var ["Z"] "modulo" Pure
  |> add_var ["Z"] "abs" Pure
  (* Bitwise operations *)
  |> add_var ["Z"] "land" Pure
  |> add_var ["Z"] "lor" Pure
  |> add_var ["Z"] "lxor" Pure
  |> add_var ["Z"] "shiftl" Pure
  |> add_var ["Z"] "shiftr" Pure
  (* Floating-point arithmetic *)
  (* String operations *)
  |> add_var ["String"] "append" Pure
  (* Character operations *)
  |> add_var ["OCaml"; "Pervasives"] "int_of_char" Pure
  |> add_var ["OCaml"; "Pervasives"] "char_of_int" Pure
  (* Unit operations *)
  |> add_var ["OCaml"; "Pervasives"] "ignore" Pure
  (* String conversion functions *)
  |> add_var ["OCaml"; "Pervasives"] "string_of_bool" Pure
  |> add_var ["OCaml"; "Pervasives"] "bool_of_string" Pure
  |> add_var ["OCaml"; "Pervasives"] "string_of_int" Pure
  |> add_var ["OCaml"; "Pervasives"] "int_of_string" Pure
  (* Pair operations *)
  |> add_var [] "fst" Pure
  |> add_var [] "snd" Pure
  (* List operations *)
  |> add_var ["OCaml"; "Pervasives"] "app" Pure
  (* Input/output *)
  (* Output functions on standard output *)
  |> add_var ["OCaml"; "Pervasives"] "print_char" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_string" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_int" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_endline" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "print_newline" (Arrow (d [[], "IO"], Pure))
  (* Output functions on standard error *)
  |> add_var ["OCaml"; "Pervasives"] "prerr_char" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_string" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_int" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_endline" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "prerr_newline" (Arrow (d [[], "IO"], Pure))
  (* Input functions on standard input *)
  |> add_var ["OCaml"; "Pervasives"] "read_line" (Arrow (d [[], "IO"], Pure))
  |> add_var ["OCaml"; "Pervasives"] "read_int" (Arrow (d [[], "IO"], Pure))
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Operations on format strings *)
  (* Program termination *)

  (* List *)
  |> add_var ["OCaml"; "List"] "length" Pure
  |> add_var ["OCaml"; "List"] "hd" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_var ["OCaml"; "List"] "tl" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_var ["OCaml"; "List"] "nth" (Arrow (d [], Arrow (d [["OCaml"], "Failure"; ["OCaml"], "Invalid_argument"], Pure)))
  |> add_var ["List"] "rev" Pure
  |> add_var ["OCaml"; "Pervasives"] "app" Pure
  |> add_var ["List"] "rev_append" Pure
  |> add_var ["OCaml"; "List"] "flatten" Pure
  (* Iterators *)
  |> add_var ["List"] "map" Pure
  |> add_var ["OCaml"; "List"] "mapi" Pure
  |> add_var ["OCaml"; "List"] "rev_map" Pure
  |> add_var ["OCaml"; "List"] "fold_left" Pure
  |> add_var ["OCaml"; "List"] "fold_right" Pure
  (* Iterators on two lists *)
  |> add_var ["OCaml"; "List"] "map2" (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))
  |> add_var ["OCaml"; "List"] "rev_map2" (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))
  |> add_var ["OCaml"; "List"] "fold_left2" (Arrow (d [], (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))))
  |> add_var ["OCaml"; "List"] "fold_right2" (Arrow (d [], (Arrow (d [], (Arrow (d [], Arrow (d [["OCaml"], "Invalid_argument"], Pure)))))))
  (* List scanning *)
  |> add_var ["List"] "forallb" Pure
  |> add_var ["List"] "existsb" Pure
  |> add_var ["OCaml"; "List"] "for_all2" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "List"] "exists2" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"; "List"] "mem" Pure
  (* List searching *)
  |> add_var ["OCaml"; "List"] "find" Pure
  |> add_var ["List"] "filter" Pure
  |> add_var ["List"] "partition" Pure
  (* Association lists *)
  (* Lists of pairs *)
  (* Sorting *)

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
    close_lift_vars = (fun _ _ -> ()) }
