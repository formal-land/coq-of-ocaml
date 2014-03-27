(** The initially opened module. *)
open FullEnvi
open Effect.Type
open SmartPrint

let env' : Effect.Type.t FullEnvi.t =
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
  |> add_typ [] "sum"
  |> add_descriptor [] "IO"
  |> add_descriptor [] "Counter"
  |> add_descriptor [] "NonTermination"

  (* The core library *)
  (* Built-in types *)
  |> add_typ [] "Z"
  |> add_typ [] "ascii"
  |> add_typ [] "string"
  |> add_typ [] "bool"
  |> add_typ [] "unit"
  |> add_typ [] "list"
  |> add_typ [] "option"
  (* Predefined exceptions *)
  |> add_exn ["OCaml"] "Match_failure"
  |> add_exn ["OCaml"] "Assert_failure"
  |> add_exn ["OCaml"] "Invalid_argument"
  |> add_exn ["OCaml"] "Failure"
  |> add_exn ["OCaml"] "Not_found"
  |> add_exn ["OCaml"] "End_of_file"
  |> add_exn ["OCaml"] "Division_by_zero"

  (* Pervasives *)
  (* Exceptions *)
  |> add_var ["OCaml"] "invalid_arg" (Arrow (d [["OCaml"], "Invalid_argument"], Pure))
  |> add_var ["OCaml"] "failwith" (Arrow (d [["OCaml"], "Failure"], Pure))
  |> add_exn ["OCaml"; "Pervasives"] "Exit"
  |> open_module

let env_typs : unit Envi.t =
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
}

let env : unit FullEnvi.t =
  { env_with_effects with
    FullEnvi.vars = Envi.map env_effects (fun _ -> ());
    close_lift_vars = (fun _ _ -> ()) }
