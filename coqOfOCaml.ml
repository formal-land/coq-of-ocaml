let parse_and_print file_name =
  Printf.printf "Parsing %s ...\n" file_name;
  let input = Pparse.preprocess file_name in
  let structure = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  ()

let main () =
  Arg.parse [] parse_and_print "Usage: ..."

;;main ()
