(** The initially opened module. *)
open Effect.Type

let effects : Effect.Env.t =
  List.fold_left (fun effects (path, x, typ) ->
    Effect.Env.add (PathName.of_name path x) typ effects)
    Effect.Env.empty
    [ [], "equiv_decb", Pure;
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
      [], "invalid_arg", Arrow (true, Pure);
      [], "failwith", Arrow (true, Pure);
      [], "print_char", Arrow (true, Pure);
      [], "print_string", Arrow (true, Pure);
      [], "print_int", Arrow (true, Pure);
      [], "print_endline", Arrow (true, Pure);
      [], "print_newline", Arrow (true, Pure);
      [], "prerr_char", Arrow (true, Pure);
      [], "prerr_string", Arrow (true, Pure);
      [], "prerr_int", Arrow (true, Pure);
      [], "prerr_endline", Arrow (true, Pure);
      [], "prerr_newline", Arrow (true, Pure);
      [], "read_line", Arrow (true, Pure);
      [], "read_int", Arrow (true, Pure) ]