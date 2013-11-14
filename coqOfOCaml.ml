open Definitions

(** Return the initial environment with the Pervasives module. *)
let initial_env () =
  Config.load_path := [Config.standard_library];
  Env.reset_cache ();
  Ident.reinit ();
  try
    Env.open_pers_signature "Pervasives" Env.initial
  with Not_found ->
    failwith "cannot open pervasives.cmi"

let parse (file_name : string) : Typedtree.structure * Types.signature =
  let env = initial_env () in
  let input = Pparse.preprocess file_name in
  let input = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  let (structure, signature, _) = Typemod.type_toplevel_phrase env input in
  (structure, signature)

let parse_and_print (file_name : string) : unit =
  let (structure, signature) = parse file_name in
  let definitions = Definitions.of_structure structure in
  (*let err = Format.err_formatter in
  Printtyped.implementation err structure;
  Printtyp.signature err signature;*)
  let std = Format.std_formatter in
  Format.fprintf std "Require Import ZArith.@\n";
  Format.fprintf std "Require Import Ascii.@\n";
  Format.fprintf std "Require Import String.@\n";
  Format.fprintf std "Require Import List.@\n";
  Format.fprintf std "Require Import Program.Basics.@\n";
  Format.fprintf std "Require Import Classes.SetoidDec.@\n@\n";
  Format.fprintf std "Local Open Scope Z_scope.@\n";
  Format.fprintf std "Import ListNotations.@\n@\n";
  Definitions.pp std definitions

let main () =
  Arg.parse [] parse_and_print "Usage: ..." (* FIXME: usage *)

;;main ()
