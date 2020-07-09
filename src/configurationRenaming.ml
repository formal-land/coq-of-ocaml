let rules = [
  (* Built-in types *)
  ("char", "ascii");
  ("()", "tt");
  ("op_coloncolon", "cons");
  ("Ok", "inl");
  ("Error", "inr");
  ("exn", "extensible_type");

  (* Predefined exceptions *)
  ("Match_failure", "OCaml.Match_failure");
  ("Assert_failure", "OCaml.Assert_failure");
  ("Invalid_argument", "OCaml.Invalid_argument");
  ("Failure", "OCaml.Failure");
  ("Not_found", "OCaml.Not_found");
  ("Out_of_memory", "OCaml.Out_of_memory");
  ("Stack_overflow", "OCaml.Stack_overflow");
  ("Sys_error", "OCaml.Sys_error");
  ("End_of_file", "OCaml.End_of_file");
  ("Division_by_zero", "OCaml.Division_by_zero");
  ("Sys_blocked_io", "OCaml.Sys_blocked_io");
  ("Undefined_recursive_module", "OCaml.Undefined_recursive_module");

  (* Optional parameters *)
  ("*predef*.None", "None");
  ("*predef*.Some", "Some");

  (* Stdlib *)
  (* Exceptions *)
  ("Stdlib.invalid_arg", "OCaml.Stdlib.invalid_arg");
  ("Stdlib.failwith", "OCaml.Stdlib.failwith");
  ("Stdlib.Exit", "OCaml.Stdlib.Exit");
  (* Comparisons *)
  ("Stdlib.op_eq", "equiv_decb");
  ("Stdlib.op_ltgt", "nequiv_decb");
  ("Stdlib.op_lt", "OCaml.Stdlib.lt");
  ("Stdlib.op_gt", "OCaml.Stdlib.gt");
  ("Stdlib.op_lteq", "OCaml.Stdlib.le");
  ("Stdlib.op_gteq", "OCaml.Stdlib.ge");
  ("Stdlib.compare", "OCaml.Stdlib.compare");
  ("Stdlib.min", "OCaml.Stdlib.min");
  ("Stdlib.max", "OCaml.Stdlib.max");
  (* Boolean operations *)
  ("Stdlib.not", "negb");
  ("Stdlib.op_andand", "andb");
  ("Stdlib.op_and", "andb");
  ("Stdlib.op_pipepipe", "orb");
  ("Stdlib.or", "orb");
  (* Integer arithmetic *)
  ("Stdlib.op_tildeminus", "Z.opp");
  ("Stdlib.op_tildeplus", "");
  ("Stdlib.succ", "Z.succ");
  ("Stdlib.pred", "Z.pred");
  ("Stdlib.op_plus", "Z.add");
  ("Stdlib.op_minus", "Z.sub");
  ("Stdlib.op_star", "Z.mul");
  ("Stdlib.op_div", "Z.div");
  ("Stdlib.__mod", "Z.modulo");
  ("Stdlib.abs", "Z.abs");
  (* Bitwise operations *)
  ("Stdlib.land", "Z.land");
  ("Stdlib.lor", "Z.lor");
  ("Stdlib.lxor", "Z.lxor");
  ("Stdlib.lsl", "Z.shiftl");
  ("Stdlib.lsr", "Z.shiftr");
  (* Floating-point arithmetic *)
  (* String operations *)
  ("Stdlib.op_caret", "String.append");
  (* Character operations *)
  ("Stdlib.int_of_char", "OCaml.Stdlib.int_of_char");
  ("Stdlib.char_of_int", "OCaml.Stdlib.char_of_int");
  (* Unit operations *)
  ("Stdlib.ignore", "OCaml.Stdlib.ignore");
  (* String conversion functions *)
  ("Stdlib.string_of_bool", "OCaml.Stdlib.string_of_bool");
  ("Stdlib.bool_of_string", "OCaml.Stdlib.bool_of_string");
  ("Stdlib.string_of_int", "OCaml.Stdlib.string_of_int");
  ("Stdlib.int_of_string", "OCaml.Stdlib.int_of_string");
  (* Pair operations *)
  ("Stdlib.fst", "fst");
  ("Stdlib.snd", "snd");
  (* List operations *)
  ("Stdlib.op_at", "OCaml.Stdlib.app");
  (* Input/output *)
  (* Output functions on standard output *)
  ("Stdlib.print_char", "OCaml.Stdlib.print_char");
  ("Stdlib.print_string", "OCaml.Stdlib.print_string");
  ("Stdlib.print_int", "OCaml.Stdlib.print_int");
  ("Stdlib.print_endline", "OCaml.Stdlib.print_endline");
  ("Stdlib.print_newline", "OCaml.Stdlib.print_newline");
  (* Output functions on standard error *)
  ("Stdlib.prerr_char", "OCaml.Stdlib.prerr_char");
  ("Stdlib.prerr_string", "OCaml.Stdlib.prerr_string");
  ("Stdlib.prerr_int", "OCaml.Stdlib.prerr_int");
  ("Stdlib.prerr_endline", "OCaml.Stdlib.prerr_endline");
  ("Stdlib.prerr_newline", "OCaml.Stdlib.prerr_newline");
  (* Input functions on standard input *)
  ("Stdlib.read_line", "OCaml.Stdlib.read_line");
  ("Stdlib.read_int", "OCaml.Stdlib.read_int");
  (* General output functions *)
  (* General input functions *)
  (* Operations on large files *)
  (* References *)
  (* Result type *)
  ("Stdlib.result", "sum");
  (* Operations on format strings *)
  (* Program termination *)

  (* Bytes *)
  ("Stdlib.Bytes.cat", "String.append");
  ("Stdlib.Bytes.concat", "String.concat");
  ("Stdlib.Bytes.length", "String.length");
  ("Stdlib.Bytes.sub", "String.sub");

  (* List *)
  ("Stdlib.List.exists", "OCaml.List._exists");
  ("Stdlib.List.exists2", "OCaml.List._exists2");
  ("Stdlib.List.length", "OCaml.List.length");
  ("Stdlib.List.map", "List.map");
  ("Stdlib.List.rev", "List.rev");

  (* Seq *)
  ("Stdlib.Seq.t", "OCaml.Seq.t");

  (* String *)
  ("Stdlib.String.length", "OCaml.String.length");
]
