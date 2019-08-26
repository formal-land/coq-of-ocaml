open Sexplib.Std
open SmartPrint

type ast = Structure.t list
  [@@deriving sexp]

let exp (structure : Typedtree.structure) : ast =
  Structure.of_structure structure

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string)
  (module_name : string) : unit =
  try
    let document =
      match mode with
      | "exp" -> !^ (Sexplib.Sexp.to_string_hum (sexp_of_ast (exp structure)))
      | "v" ->
        concat (List.map (fun d -> d ^^ newline) [
          !^ "Require Import OCaml.OCaml." ^^ newline;
          !^ "Local Open Scope Z_scope.";
          !^ "Local Open Scope type_scope.";
          !^ "Import ListNotations."]) ^^ newline ^^
        Structure.to_coq (exp structure)
      | _ -> failwith (Printf.sprintf "Unknown mode '%s'." mode) in
    to_stdout 80 2 document;
    print_newline ();
    flush stdout with
  | Error.Make x ->
    prerr_endline @@ Pp.to_string (!^ "Error:" ^^ Error.pp x)

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure; cmt_loadpath } ->
    (* We set the [load_path] so that the OCaml compiler can import the environments
       from the [.cmt] files. This is required to specify were to find the definitions
       of the standard library. See https://discuss.ocaml.org/t/getting-the-environment-from-the-ast-in-cmt/4287 *)
    Config.load_path := cmt_loadpath;
    structure
  | _ -> failwith "Cannot extract cmt data."

let module_name (file_name : string) : string =
  String.capitalize_ascii @@ Filename.chop_extension @@ Filename.basename file_name

(** The main function. *)
let main () =
  let file_name = ref None in
  let mode = ref "" in
  let options = [
    "-mode", Arg.Set_string mode, " v (generate Coq .v files, you probably want this option), exp (the simplified expression tree)"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name) !mode (module_name file_name);

;;main ()
