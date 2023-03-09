module Output = struct
  type t = {
    error_message : string;
    generated_file : (string * string) option;
    has_errors : bool;
    source_file_name : string;
    success_message : string;
  }

  let write (json_mode : bool) (output : t) : unit =
    if json_mode then
      let error_file_name = output.source_file_name ^ ".errors" in
      Util.File.write error_file_name output.error_message
    else if output.has_errors then print_endline output.error_message;
    print_endline output.success_message;
    match output.generated_file with
    | None -> ()
    | Some (generated_file_name, generated_file_content) ->
        Util.File.write generated_file_name generated_file_content
end

let exp (context : MonadEval.Context.t) (typedtree : Mtyper.typedtree)
    (typedtree_errors : exn list) (source_file_name : string)
    (source_file_content : string) (json_mode : bool) :
    Ast.t * MonadEval.Import.t list * string * bool =
  let { MonadEval.Result.errors; imports; value; _ } =
    MonadEval.eval (Ast.of_typedtree typedtree typedtree_errors) context
  in
  let error_message =
    Error.display_errors json_mode source_file_name source_file_content errors
  in
  let has_errors = match errors with [] -> false | _ :: _ -> true in
  (value, imports, error_message, has_errors)

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (context : MonadEval.Context.t) (typedtree : Mtyper.typedtree)
    (typedtree_errors : exn list) (source_file_name : string)
    (source_file_content : string) (output_file_name : string option)
    (json_mode : bool) : Output.t =
  let ast, imports, error_message, has_errors =
    exp context typedtree typedtree_errors source_file_name source_file_content
      json_mode
  in
  let document = Ast.to_coq imports ast in
  let generated_file_name =
    match output_file_name with
    | None ->
        let without_extension = Filename.remove_extension source_file_name in
        let extension = Filename.extension source_file_name in
        let new_extension =
          match extension with
          | ".ml" -> ".v"
          | ".mli" -> "_mli.v"
          | _ ->
              failwith
                ("Unexpected extension " ^ extension ^ " for the file "
               ^ source_file_name)
        in
        Filename.concat
          (Filename.dirname without_extension)
          (String.capitalize_ascii (Filename.basename without_extension))
        ^ new_extension
    | Some output_file_name -> output_file_name
  in
  let generated_file_content = SmartPrint.to_string 80 2 document in
  let success_message =
    if has_errors then
      Error.colorize "31" "❌" ^ " "
      ^ Printf.sprintf "File '%s' generated with some errors"
          generated_file_name
    else
      Error.colorize "32" "✔️"
      ^ " "
      ^ Printf.sprintf "File '%s' successfully generated" generated_file_name
  in
  {
    error_message;
    generated_file = Some (generated_file_name, generated_file_content);
    has_errors;
    source_file_name;
    success_message;
  }

let exit (context : MonadEval.Context.t) (output : Output.t) : unit =
  let is_blacklist =
    Configuration.is_filename_in_error_blacklist context.configuration
  in
  if output.has_errors && not is_blacklist then exit 1 else exit 0

(** The main function. *)
let main () =
  Printexc.record_backtrace true;
  let file_name = ref None in
  let json_mode = ref false in
  let configuration_file_name = ref None in
  let output_file_name = ref None in
  let options =
    [
      ( "-config",
        Arg.String (fun value -> configuration_file_name := Some value),
        "file   the configuration file of coq-of-ocaml" );
      ( "-output",
        Arg.String (fun value -> output_file_name := Some value),
        "file   the name of the .v file to output" );
      ( "-json-mode",
        Arg.Set json_mode,
        "    produce the list of error messages in a JSON file" );
    ]
  in
  let usage_msg = "Usage:\n  coq-of-ocaml [options] file.ml(i)\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
      let base_name = Filename.basename file_name in
      let directory_name = Filename.dirname file_name in

      let configuration =
        Configuration.of_optional_file_name file_name !configuration_file_name
      in

      let merlin_config =
        Mconfig.get_external_config file_name Mconfig.initial
      in
      let merlin_config =
        {
          merlin_config with
          query =
            {
              merlin_config.query with
              directory = directory_name;
              filename = base_name;
            };
        }
      in

      let file_channel = open_in file_name in
      let file_size = in_channel_length file_channel in
      let file_content = really_input_string file_channel file_size in
      close_in file_channel;
      let file_source = Msource.make file_content in

      let pipeline = Mpipeline.make merlin_config file_source in

      Mpipeline.with_pipeline pipeline (fun _ ->
          let comments = Mpipeline.reader_comments pipeline in
          let typing = Mpipeline.typer_result pipeline in
          let typedtree = Mtyper.get_typedtree typing in
          let typedtree_errors = Mtyper.get_errors typing in
          let initial_loc = Ast.get_initial_loc typedtree in
          let initial_env = Mtyper.get_env typing in

          let context =
            MonadEval.Context.init comments configuration initial_env
              initial_loc
          in

          let output =
            of_ocaml context typedtree typedtree_errors file_name file_content
              !output_file_name !json_mode
          in
          Output.write !json_mode output;
          exit context output)
;;

main ()
