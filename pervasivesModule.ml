(** The initially opened module. *)
open Effect.Type

let effects : Effect.Env.t =
  let exn_invalid_argument = Effect.Descriptor.of_atom
    { Effect.Atom.name = PathName.of_name [] "Invalid_argument";
      kind = Effect.Atom.Kind.Error;
      coq_type = "string" } in
  let exn_failure = Effect.Descriptor.of_atom
    { Effect.Atom.name = PathName.of_name [] "Failure";
      kind = Effect.Atom.Kind.Error;
      coq_type = "string" } in
  let io = Effect.Descriptor.of_atom
    { Effect.Atom.name = PathName.of_name [] "IO";
      kind = Effect.Atom.Kind.State;
      coq_type = "list string * list string" } in
  let counter = Effect.Descriptor.of_atom
    { Effect.Atom.name = PathName.of_name [] "Counter";
      kind = Effect.Atom.Kind.State;
      coq_type = "nat" } in
  let non_termination = Effect.Descriptor.of_atom
    { Effect.Atom.name = PathName.of_name [] "NonTermination";
      kind = Effect.Atom.Kind.Error;
      coq_type = "unit" } in
  List.fold_left (fun effects (path, x, typ) ->
    Effect.Env.add (PathName.of_name path x) typ effects)
    Effect.Env.empty
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
      [], "invalid_arg", Arrow (exn_invalid_argument, Pure);
      [], "failwith", Arrow (exn_failure, Pure);
      [], "print_char", Arrow (io, Pure);
      [], "print_string", Arrow (io, Pure);
      [], "print_int", Arrow (io, Pure);
      [], "print_endline", Arrow (io, Pure);
      [], "print_newline", Arrow (io, Pure);
      [], "prerr_char", Arrow (io, Pure);
      [], "prerr_string", Arrow (io, Pure);
      [], "prerr_int", Arrow (io, Pure);
      [], "prerr_endline", Arrow (io, Pure);
      [], "prerr_newline", Arrow (io, Pure);
      [], "read_line", Arrow (io, Pure);
      [], "read_int", Arrow (io, Pure);
      [], "read_counter", Arrow (counter, Pure);
      [], "not_terminated", Arrow (non_termination, Pure) ]