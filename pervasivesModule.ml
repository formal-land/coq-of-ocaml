(** The initially opened module. *)
open Effect.Type
open SmartPrint

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
      [], "list" ]

let env_descriptors : unit Envi.t =
  Envi.open_module @@
  List.fold_left (fun env_descriptors (path, base) ->
    Envi.add (PathName.of_name path base) () env_descriptors)
    Envi.empty
    [ [], "Invalid_argument";
      [], "Failure";
      [], "IO";
      [], "Counter";
      [], "NonTermination" ]

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
      [], "[]";
      [], "cons" ]

let env_fields : unit Envi.t =
  Envi.open_module Envi.empty

let env_effects : Effect.Type.t Envi.t =
  let descriptor x =
    let loc = Loc.Ether x in
    let x = {
      BoundName.path_name = PathName.of_name [] x;
      depth = 0 } in
    Effect.Descriptor.singleton loc x in
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
      [], "append", Pure;
      [], "int_of_char", Pure;
      [], "char_of_int", Pure;
      [], "ignore", Pure;
      [], "fst", Pure;
      [], "snd", Pure;
      [], "app", Pure;
      [], "invalid_arg", Arrow (descriptor "Invalid_argument", Pure);
      [], "failwith", Arrow (descriptor "Failure", Pure);
      [], "print_char", Arrow (descriptor "IO", Pure);
      [], "print_string", Arrow (descriptor "IO", Pure);
      [], "print_int", Arrow (descriptor "IO", Pure);
      [], "print_endline", Arrow (descriptor "IO", Pure);
      [], "print_newline", Arrow (descriptor "IO", Pure);
      [], "prerr_char", Arrow (descriptor "IO", Pure);
      [], "prerr_string", Arrow (descriptor "IO", Pure);
      [], "prerr_int", Arrow (descriptor "IO", Pure);
      [], "prerr_endline", Arrow (descriptor "IO", Pure);
      [], "prerr_newline", Arrow (descriptor "IO", Pure);
      [], "read_line", Arrow (descriptor "IO", Pure);
      [], "read_int", Arrow (descriptor "IO", Pure);
      [], "read_counter", Arrow (descriptor "Counter", Pure);
      [], "not_terminated", Arrow (descriptor "NonTermination", Pure) ]

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
