let parse_and_print file_name =
  Printf.printf "Parsing %s:\n" file_name;
  let env = Env.initial in
  let input = Pparse.preprocess file_name in
  let input = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  let (structure, signature, env) = Typemod.type_toplevel_phrase env input in
  Printtyp.signature Format.str_formatter signature;
  let signature = Format.flush_str_formatter () in
  Printtyped.implementation Format.str_formatter structure;
  let structure = Format.flush_str_formatter () in
  print_endline signature;
  print_endline structure

let main () =
  Arg.parse [] parse_and_print "Usage: ..."

;;main ()
