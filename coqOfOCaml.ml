(** Display an OCaml structure on stdout converted in Coq. *)
let of_ocaml (structure : Typedtree.structure) : unit =
  let definition = Definition.of_structure structure in
  let std = Format.std_formatter in
  Format.fprintf std "Require Import ZArith.@\n";
  Format.fprintf std "Require Import Ascii.@\n";
  Format.fprintf std "Require Import String.@\n";
  Format.fprintf std "Require Import List.@\n";
  Format.fprintf std "Require Import Program.Basics.@\n";
  Format.fprintf std "Require Import Classes.SetoidDec.@\n@\n";
  Format.fprintf std "Local Open Scope Z_scope.@\n";
  Format.fprintf std "Import ListNotations.@\n";
  Format.fprintf std "Set Implicit Arguments.@\n@\n";
  Definition.pp std definition

(** Display an OCaml structure on stdout using the OCaml's pretty-printer. *)
let pp_ocaml (structure : Typedtree.structure) : unit =
  Printtyped.implementation Format.std_formatter structure

(** Parse a .ml file to a typed AST. *)
let parse_ml (file_name : string) : Typedtree.structure =
  (* The initial environment with the Pervasives module. *)
  let env =
    Config.load_path := [Config.standard_library];
    Env.reset_cache ();
    Ident.reinit ();
    try
      Env.open_pers_signature "Pervasives" Env.initial
    with Not_found ->
      failwith "cannot open pervasives.cmi" in
  let input = Pparse.preprocess file_name in
  let input = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  let (structure, _, _) = Typemod.type_toplevel_phrase env input in
  structure

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } -> structure
  | _ -> failwith "Cannot extract cmt data."

(** The main function. *)
let main () =
  Arg.parse [] (fun file_name -> of_ocaml (parse_cmt file_name)) "Usage: ..." (* FIXME: usage *)

;;main ()
