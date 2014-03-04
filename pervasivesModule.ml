(** The initially opened module. *)
open Effect.Type
open SmartPrint

let env_atoms : Common.env_atoms =
  List.fold_left (fun env_atoms (x, kind, coq_type) ->
    PathName.Env.add_name x { Effect.Atom.kind = kind; coq_type = coq_type }
      env_atoms)
    PathName.Env.empty
    [ "Invalid_argument", Effect.Atom.Kind.Error, !^ "string" ]

let env_effects : Common.env_effects =
  (*let exn_invalid_argument = Effect.Descriptor.of_atom
    { Effect.Atom.name = "Invalid_argument";
      kind = Effect.Atom.Kind.Error;
      coq_type = !^ "string" } in
  let exn_failure = Effect.Descriptor.of_atom
    { Effect.Atom.name = "Failure";
      kind = Effect.Atom.Kind.Error;
      coq_type = !^ "string" } in
  let io = Effect.Descriptor.of_atom
    { Effect.Atom.name = "IO";
      kind = Effect.Atom.Kind.State;
      coq_type = !^ "list string * list string" } in
  let counter = Effect.Descriptor.of_atom
    { Effect.Atom.name = "Counter";
      kind = Effect.Atom.Kind.State;
      coq_type = !^ "nat" } in
  let non_termination = Effect.Descriptor.of_atom
    { Effect.Atom.name = "NonTermination";
      kind = Effect.Atom.Kind.Error;
      coq_type = !^ "unit" } in*)
  let descriptor x = Effect.Descriptor.singleton (PathName.of_name [] x) in
  List.fold_left (fun env_effects (path, x, typ) ->
    PathName.Env.add (PathName.of_name path x) typ env_effects)
    PathName.Env.empty
    [ [], "tt", Pure;
      [], "equiv_decb", Pure;
      [], "nequiv_decb", Pure;
      ["Z"], "ltb", Pure;
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