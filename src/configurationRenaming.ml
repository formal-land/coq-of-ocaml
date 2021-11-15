let rules =
  [
    (* Built-in types *)
    ("()", "tt");
    ("op_coloncolon", "cons");
    ("Ok", "inl");
    ("Error", "inr");
    (* Predefined exceptions *)
    ("Match_failure", "CoqOfOCaml.Match_failure");
    ("Assert_failure", "CoqOfOCaml.Assert_failure");
    ("Invalid_argument", "CoqOfOCaml.Invalid_argument");
    ("Failure", "CoqOfOCaml.Failure");
    ("Not_found", "CoqOfOCaml.Not_found");
    ("Out_of_memory", "CoqOfOCaml.Out_of_memory");
    ("Stack_overflow", "CoqOfOCaml.Stack_overflow");
    ("Sys_error", "CoqOfOCaml.Sys_error");
    ("End_of_file", "CoqOfOCaml.End_of_file");
    ("Division_by_zero", "CoqOfOCaml.Division_by_zero");
    ("Sys_blocked_io", "CoqOfOCaml.Sys_blocked_io");
    ("Undefined_recursive_module", "CoqOfOCaml.Undefined_recursive_module");
    (* Optional parameters *)
    ("*predef*.None", "None");
    ("*predef*.Some", "Some");
    (* Stdlib *)
    (* Exceptions *)
    ("Stdlib.invalid_arg", "CoqOfOCaml.Stdlib.invalid_arg");
    ("Stdlib.failwith", "CoqOfOCaml.Stdlib.failwith");
    ("Stdlib.Exit", "CoqOfOCaml.Stdlib.Exit");
    (* Comparisons *)
    ("Stdlib.op_eq", "equiv_decb");
    ("Stdlib.op_ltgt", "nequiv_decb");
    ("Stdlib.op_lt", "CoqOfOCaml.Stdlib.lt");
    ("Stdlib.op_gt", "CoqOfOCaml.Stdlib.gt");
    ("Stdlib.op_lteq", "CoqOfOCaml.Stdlib.le");
    ("Stdlib.op_gteq", "CoqOfOCaml.Stdlib.ge");
    ("Stdlib.compare", "CoqOfOCaml.Stdlib.compare");
    ("Stdlib.min", "CoqOfOCaml.Stdlib.min");
    ("Stdlib.max", "CoqOfOCaml.Stdlib.max");
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
    ("Stdlib._mod", "Z.modulo");
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
    ("Stdlib.int_of_char", "CoqOfOCaml.Stdlib.int_of_char");
    ("Stdlib.char_of_int", "CoqOfOCaml.Stdlib.char_of_int");
    (* Unit operations *)
    ("Stdlib.ignore", "CoqOfOCaml.Stdlib.ignore");
    (* String conversion functions *)
    ("Stdlib.string_of_bool", "CoqOfOCaml.Stdlib.string_of_bool");
    ("Stdlib.bool_of_string", "CoqOfOCaml.Stdlib.bool_of_string");
    ("Stdlib.string_of_int", "CoqOfOCaml.Stdlib.string_of_int");
    ("Stdlib.int_of_string", "CoqOfOCaml.Stdlib.int_of_string");
    (* Pair operations *)
    ("Stdlib.fst", "fst");
    ("Stdlib.snd", "snd");
    (* List operations *)
    ("Stdlib.op_at", "CoqOfOCaml.Stdlib.app");
    (* Input/output *)
    (* Output functions on standard output *)
    ("Stdlib.print_char", "CoqOfOCaml.Stdlib.print_char");
    ("Stdlib.print_string", "CoqOfOCaml.Stdlib.print_string");
    ("Stdlib.print_int", "CoqOfOCaml.Stdlib.print_int");
    ("Stdlib.print_endline", "CoqOfOCaml.Stdlib.print_endline");
    ("Stdlib.print_newline", "CoqOfOCaml.Stdlib.print_newline");
    (* Output functions on standard error *)
    ("Stdlib.prerr_char", "CoqOfOCaml.Stdlib.prerr_char");
    ("Stdlib.prerr_string", "CoqOfOCaml.Stdlib.prerr_string");
    ("Stdlib.prerr_int", "CoqOfOCaml.Stdlib.prerr_int");
    ("Stdlib.prerr_endline", "CoqOfOCaml.Stdlib.prerr_endline");
    ("Stdlib.prerr_newline", "CoqOfOCaml.Stdlib.prerr_newline");
    (* Input functions on standard input *)
    ("Stdlib.read_line", "CoqOfOCaml.Stdlib.read_line");
    ("Stdlib.read_int", "CoqOfOCaml.Stdlib.read_int");
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
    ("Stdlib.List.exists", "CoqOfOCaml.List._exists");
    ("Stdlib.List.exists2", "CoqOfOCaml.List._exists2");
    ("Stdlib.List.length", "CoqOfOCaml.List.length");
    ("Stdlib.List.map", "List.map");
    ("Stdlib.List.rev", "List.rev");
    (* Seq *)
    ("Stdlib.Seq.t", "CoqOfOCaml.Seq.t");
    (* String *)
    ("Stdlib.String.length", "CoqOfOCaml.String.length");
  ]
