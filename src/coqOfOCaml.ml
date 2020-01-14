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
  (typedtree : Mtyper.typedtree)
  (typedtree_errors : exn list)
  (source_file_name : string)
  (source_file_content : string)
  (json_mode : bool)
  : Ast.t * string option =
  let { MonadEval.Result.errors; value} =
    MonadEval.eval
      source_file_name
      (Ast.of_typedtree typedtree typedtree_errors)
      env
      loc
      None in
  let error_message =
    match errors with
    | [] -> None
    | _ :: _ -> Some (Error.display_errors json_mode source_file_name source_file_content errors) in
  (value, error_message)

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml
  (env : Env.t)
  (loc : Loc.t)
  (typedtree : Mtyper.typedtree)
  (typedtree_errors : exn list)
  (source_file_name : string)
  (source_file_content : string)
  (output_file_name : string option)
  (json_mode : bool)
  : Output.t =
  let (ast, error_message) =
    exp env loc typedtree typedtree_errors source_file_name source_file_content json_mode in
  let document = Ast.to_coq ast in
  let generated_file_name =
    match output_file_name with
    | None ->
      let source_file_name_without_extension = Filename.remove_extension source_file_name in
      let extension = Filename.extension source_file_name in
      let new_extension =
        match extension with
        | ".ml" -> ".v"
        | ".mli" -> "_mli.v"
        | _ ->
          failwith (
            "Unexpected extension " ^ extension ^ " for the file " ^
            source_file_name
          ) in
      source_file_name_without_extension ^ new_extension
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

(** The main function. *)
let main () =
  Printexc.record_backtrace true;
  let file_name = ref None in
  let json_mode = ref false in
  let merlin_file_name = ref None in
  let output_file_name = ref None in
  let options = [
    (
      "-merlin",
      Arg.String (fun value -> merlin_file_name := Some value),
      "file   the configuration file of Merlin"
    );
    (
      "-output",
      Arg.String (fun value -> output_file_name := Some value),
      "file   the name of the .v file to output"
    );
    (
      "-json-mode",
      Arg.Set json_mode,
      "    produce the list of error messages in JSON"
    )
  ] in
  let usage_msg = "Usage:\n  coq-of-ocaml [options] file.ml\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
    let base_name = Filename.basename file_name in
    let directory_name = Filename.dirname file_name in
    let merlin_file_name =
      match !merlin_file_name with
      | None -> Filename.concat directory_name ".merlin"
      | Some merlin_file_name -> merlin_file_name in
    let merlin_config = Mconfig.load_dotmerlins ~filenames:[merlin_file_name] Mconfig.initial in
    let merlin_config = {
      merlin_config with
      query = {
        merlin_config.query with
        directory = directory_name;
        filename = base_name
      }
    } in

    let file_channel = open_in file_name in
    let file_size = in_channel_length file_channel in
    let file_content = really_input_string file_channel file_size in
    close_in file_channel;
    let file_source = Msource.make file_content in

    let pipeline = Mpipeline.make merlin_config file_source in
    let typing = Mpipeline.typer_result pipeline in
    let typedtree = Mtyper.get_typedtree typing in
    let typedtree_errors = Mtyper.get_errors typing in
    let initial_loc = Ast.get_initial_loc typedtree in
    let initial_env = Mtyper.get_env typing in
    let output =
      of_ocaml initial_env initial_loc typedtree typedtree_errors file_name file_content !output_file_name !json_mode in
    Output.write output

;;main ()
