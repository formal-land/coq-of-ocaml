open SmartPrint

type ast = Structure.t list

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
  (source_file_name : string)
  (source_file_content : string)
  : ast option * string option =
  let { MonadEval.Result.errors; value} =
    MonadEval.eval source_file_name (Structure.of_structure structure) env loc in
  let error_message =
    match errors with
    | [] -> None
    | _ :: _ -> Some (Error.display_errors source_file_name source_file_content errors) in
  (Some value, error_message)

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml
  (env : Env.t)
  (loc : Loc.t)
  (structure : Typedtree.structure)
  (source_file_name : string)
  (source_file_content : string)
  (output_file_name : string option)
  : Output.t =
  let (ast, error_message) = exp env loc structure source_file_name source_file_content in
  match ast with
  | None ->
    {
      error_message;
      generated_file = None;
      success_message = None;
    }
  | Some ast ->
    let document =
      concat (List.map (fun d -> d ^^ newline) [
        !^ "Require Import OCaml.OCaml." ^^ newline;
        !^ "Local Open Scope Z_scope.";
        !^ "Local Open Scope type_scope.";
        !^ "Import ListNotations."]) ^^ newline ^^
      Structure.to_coq ast in
    let generated_file_name =
      match output_file_name with
      | None -> Filename.remove_extension source_file_name ^ ".v"
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
    )
  ] in
  let usage_msg = "Usage:\n  ./coqOfOCaml.native [options] file.ml\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name ->
    let merlin_file_name =
      match !merlin_file_name with
      | None -> Filename.concat (Filename.dirname file_name) ".merlin"
      | Some merlin_file_name -> merlin_file_name in
    let merlin_config = Mconfig.load_dotmerlins ~filenames:[merlin_file_name] Mconfig.initial in

    let file_channel = open_in file_name in
    let file_size = in_channel_length file_channel in
    let file_content = really_input_string file_channel file_size in
    close_in file_channel;
    let file_source = Msource.make file_content in

    let pipeline = Mpipeline.make merlin_config file_source in
    let typing = Mpipeline.typer_result pipeline in
    let initial_env = Mtyper.get_env typing in
    begin match Mtyper.get_typedtree typing with
    | `Implementation structure ->
    let initial_loc =
      match structure.str_items with
      | structure_item :: _ -> Loc.of_location structure_item.str_loc
      | [] -> failwith "Unexpected empty file" in
      let output = of_ocaml initial_env initial_loc structure file_name file_content !output_file_name in
      Output.write output
    | `Interface _ -> failwith "Unexpected interface"
    end

;;main ()
