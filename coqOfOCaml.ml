open SmartPrint

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) : unit =
  let (definition, _) = Structure.of_structure structure [] PathName.Map.empty in
  let document =
    concat (List.map (fun d -> d ^^ newline) [
      !^ "Require Import CoqOfOCaml." ^^ newline;
      !^ "Local Open Scope Z_scope.";
      !^ "Import ListNotations.";
      !^ "Set Implicit Arguments."]) ^^ newline ^^
    Structure.to_coq definition in
  to_stdout 80 2 document;
  print_newline ();
  flush stdout

(** Display an OCaml structure on stdout using the OCaml's pretty-printer. *)
let pp_ocaml (structure : Typedtree.structure) : unit =
  Printtyped.implementation Format.std_formatter structure

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } -> structure
  | _ -> failwith "Cannot extract cmt data."

(** The main function. *)
let main () =
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  let file_name = ref None in
  Arg.parse [] (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage [] usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name);
  (*print_newline ();
  to_stdout 80 2 @@ Structure.pp [PervasivesModule.pervasives]*)

;;main ()