open Sexplib.Std
open SmartPrint

type ast = Structure.t list
  [@@deriving sexp]

let exp
  (env : Env.t)
  (loc : Loc.t)
  (structure : Typedtree.structure)
  (source_file : string)
  : ast option =
  try
    let { MonadEval.Result.errors; value} = MonadEval.eval (Structure.of_structure structure) env loc in
    begin if errors <> [] then
      Error.display_errors source_file errors
    end;
    Some value with
  | Envaux.Error (Module_not_found path) ->
    prerr_endline ("Fatal error: module '" ^ Path.name path ^ "' not found while importing environments");
    None

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml
  (env : Env.t)
  (loc : Loc.t)
  (structure : Typedtree.structure)
  (source_file : string)
  (mode : string)
  : unit =
  match exp env loc structure source_file with
  | None -> ()
  | Some ast ->
    let document =
      match mode with
      | "exp" -> !^ (Sexplib.Sexp.to_string_hum (sexp_of_ast ast))
      | "v" ->
        concat (List.map (fun d -> d ^^ newline) [
          !^ "Require Import OCaml.OCaml." ^^ newline;
          !^ "Local Open Scope Z_scope.";
          !^ "Local Open Scope type_scope.";
          !^ "Import ListNotations."]) ^^ newline ^^
        Structure.to_coq ast
      | _ -> failwith (Printf.sprintf "Unknown mode '%s'." mode) in
    to_stdout 80 2 document;
    print_newline ();
    flush stdout

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (build_dir : string) (file_name : string)
  : Env.t * Loc.t * Typedtree.structure * string =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some {
    Cmt_format.cmt_annots = Cmt_format.Implementation structure;
    cmt_initial_env;
    cmt_loadpath;
    cmt_sourcefile = Some source_file;
    cmt_imports
  } ->
    (* We set the [load_path] so that the OCaml compiler can import the environments
       from the [.cmt] files. This is required to specify were to find the definitions
       of the standard library. See https://discuss.ocaml.org/t/getting-the-environment-from-the-ast-in-cmt/4287 *)
    Config.load_path := cmt_loadpath;
    (* We load some .cmi files needed for name resolution. *)
    cmt_imports |> List.iter (fun (path, _) ->
      let load_path = build_dir :: !Config.load_path in
      let cmt_file =
        match Misc.find_in_path_uncap load_path (path ^ ".cmt") with
        | cmt_file -> Some cmt_file
        | exception Not_found -> None in
      (* Check that we are not importing ourselves. *)
      if cmt_file <> Some file_name then begin
        let cmi_file = Misc.find_in_path_uncap load_path (path ^ ".cmi") in
        let _ = Env.read_signature path cmi_file in
        ()
      end
    );
    let initial_loc =
      match structure.str_items with
      | structure_item :: _ -> Loc.of_location structure_item.str_loc
      | [] -> failwith "Unexpected empty file" in
    (cmt_initial_env, initial_loc, structure, source_file)
  | _ -> failwith "Cannot extract cmt data"

(** The main function. *)
let main () =
  let file_name = ref None in
  let build_dir = ref "" in
  let mode = ref "" in
  let options = [
    "-build-dir", Arg.Set_string build_dir, "the build directory";
    "-mode", Arg.Set_string mode, " v (generate Coq .v files, you probably want this option), exp (the simplified expression tree)"
  ] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
    let (env, loc, structure, source_file) = parse_cmt !build_dir file_name in
    of_ocaml env loc structure source_file !mode;

;;main ()
