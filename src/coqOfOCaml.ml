open Sexplib.Std
open SmartPrint

type ast = Structure.t list
  [@@deriving sexp]

module Mode = struct
  type t =
    | Exp
    | V

  let of_string (mode : string) : t option=
    match mode with
    | "exp" -> Some Exp
    | "v" -> Some V
    | _ -> None

  let get_extension (mode : t): string =
    match mode with
    | Exp -> ".exp"
    | V -> ".v"

  let get_output_file_name (mode : t) (source_file_name : string) : string =
    Filename.remove_extension (Filename.basename source_file_name) ^ (get_extension mode)
end

module Output = struct
  type t = {
    error_message : string option;
    generated_file : (string * string) option;
    success_message : string option;
  }

  let write (output : t) : unit =
    let { error_message; generated_file; success_message } = output in
    begin match error_message with
    | None -> ()
    | Some error_message -> prerr_endline error_message
    end;
    begin match success_message with
    | None -> ()
    | Some success_message -> print_endline success_message
    end;
    begin match generated_file with
    | None -> ()
    | Some (generated_file_name, generated_file_content) ->
      let output_channel = open_out generated_file_name in
      output_string output_channel generated_file_content;
      close_out output_channel
    end
end

let exp
  (env : Env.t)
  (loc : Loc.t)
  (structure : Typedtree.structure)
  (source_file : string)
  : ast option * string option =
  try
    let { MonadEval.Result.errors; value} = MonadEval.eval (Structure.of_structure structure) env loc in
    let error_message =
      match errors with
      | [] -> None
      | _ :: _ -> Some (Error.display_errors source_file errors) in
    (Some value, error_message) with
  | Envaux.Error (Module_not_found path) ->
    (None, Some ("Fatal error: module '" ^ Path.name path ^ "' not found while importing environments"))

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml
  (env : Env.t)
  (loc : Loc.t)
  (structure : Typedtree.structure)
  (source_file : string)
  (source_file_name : string)
  (mode : string)
  (output_file_name : string option)
  : Output.t =
  match Mode.of_string mode with
  | None ->
    {
      error_message = Some (Printf.sprintf "Unknown mode '%s'" mode);
      generated_file = None;
      success_message = None;
    }
  | Some mode ->
    let (ast, error_message) = exp env loc structure source_file in
    begin match ast with
    | None ->
      {
        error_message;
        generated_file = None;
        success_message = None;
      }
    | Some ast ->
      let document =
        match mode with
        | Mode.Exp -> !^ (Sexplib.Sexp.to_string_hum (sexp_of_ast ast))
        | Mode.V ->
          concat (List.map (fun d -> d ^^ newline) [
            !^ "Require Import OCaml.OCaml." ^^ newline;
            !^ "Local Open Scope Z_scope.";
            !^ "Local Open Scope type_scope.";
            !^ "Import ListNotations."]) ^^ newline ^^
          Structure.to_coq ast in
      let generated_file_name =
        match output_file_name with
        | None -> Mode.get_output_file_name mode source_file_name
        | Some output_file_name -> output_file_name in
      let generated_file_content = SmartPrint.to_string 80 2 document in
      let success_message =
        match error_message with
        | None ->
          Some (Printf.sprintf "File '%s' successfully generated" generated_file_name)
        | Some _ ->
          Some (Printf.sprintf "File '%s' generated with some errors" generated_file_name) in
      {
        error_message;
        generated_file = Some (generated_file_name, generated_file_content);
        success_message;
      }
    end

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
    cmt_imports;
    _
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
  let build_dir = ref None in
  let mode = ref None in
  let output_file_name = ref None in
  let options = [
    (
      "-build-dir",
      Arg.String (fun value -> build_dir := Some value),
      "dir  the build directory, where the other .cmt files are"
    );
    (
      "-mode",
      Arg.String (fun value -> mode := Some value),
      "[v|exp]   v to generate a Coq .v file (default), exp to generate an AST .exp file (for debugging)"
    );
    (
      "-output",
      Arg.String (fun value -> output_file_name := Some value),
      "file    the name of the file to output"
    )
  ] in
  let usage_msg = "Usage:\n  ./coqOfOCaml.native [options] file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
    let build_dir = match !build_dir with None -> Filename.dirname file_name | Some build_dir -> build_dir in
    let mode = match !mode with None -> "v" | Some mode -> mode in
    let (env, loc, structure, source_file) = parse_cmt build_dir file_name in
    let output = of_ocaml env loc structure source_file file_name mode !output_file_name in
    Output.write output

;;main ()
