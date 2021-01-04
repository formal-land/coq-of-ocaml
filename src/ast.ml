(** The AST of a [.ml] or [.mli]. *)
open SmartPrint
open Monad.Notations

type content =
  | SignatureAxioms of SignatureAxioms.t
  | Structure of Structure.t list

type t = {
  content : content;
  head_suffix : string;
  without_guard_checking : bool;
  without_positivity_checking : bool;
}

let get_initial_loc (typedtree : Mtyper.typedtree) : Location.t =
  match typedtree with
  | `Implementation structure ->
    begin match structure.str_items with
    | structure_item :: _ -> structure_item.str_loc
    | [] -> failwith "Unexpected empty file"
    end
  | `Interface signature ->
    begin match signature.sig_items with
    | signature_item :: _ -> signature_item.sig_loc
    | [] -> failwith "Unexpected empty file"
    end

let report_errors (typedtree_errors : exn list) : unit Monad.t =
  typedtree_errors |> Monad.List.iter (fun exn ->
    let error = Location.error_of_exn exn in
    match error with
    | Some (`Ok error) ->
      let loc = Location.loc_of_report error in
      let error_buffer = Buffer.create 0 in
      Location.print_report (Format.formatter_of_buffer error_buffer) error;
      set_loc loc (raise () Error.Category.Merlin (Buffer.contents error_buffer))
    | _ -> return ()
  )

let of_typedtree (typedtree : Mtyper.typedtree) (typedtree_errors : exn list)
  : t Monad.t =
  report_errors typedtree_errors >>
  begin match typedtree with
  | `Implementation structure ->
    Structure.of_structure structure >>= fun structure ->
    return (Structure structure)
  | `Interface signature ->
    SignatureAxioms.of_signature signature >>= fun signature ->
    return (SignatureAxioms signature)
  end >>= fun content ->
  get_configuration >>= fun configuration ->
  return {
    content;
    head_suffix = configuration.head_suffix;
    without_guard_checking =
      Configuration.is_without_guard_checking configuration;
    without_positivity_checking =
      Configuration.is_without_positivity_checking configuration;
  }

let to_coq (imports : MonadEval.Import.t list) (ast : t) : SmartPrint.t =
  concat (List.map (fun d -> d ^^ newline) [
    !^ "Require Import OCaml.OCaml." ^^ newline;
    !^ "Set Primitive Projections.";
    !^ "Set Printing Projections.";
    !^ "Open Scope string_scope.";
    !^ "Open Scope Z_scope.";
    !^ "Open Scope type_scope.";
    !^ "Import ListNotations.";
  ]) ^^
  begin if ast.without_guard_checking then
    !^ "Unset Guard Checking." ^^ newline
  else
    empty
  end ^^
  begin if ast.without_positivity_checking then
    !^ "Unset Positivity Checking." ^^ newline
  else
    empty
  end ^^ newline ^^
  begin match imports with
  | [] -> empty
  | _ :: _ ->
    separate empty (imports |> List.map (
      fun { MonadEval.Import.base; import; mli; name } ->
        let name_to_require = if mli then name ^ "_mli" else name in
        nest (
          !^ "Require" ^^ !^ base ^-^ !^ "." ^-^ !^ name_to_require ^-^ !^ "." ^^
          begin if mli then
            nest (
              !^ "Module" ^^ !^ name ^^ !^ ":=" ^^ !^ name_to_require ^-^ !^ "."
            )
          else
            empty
          end
        )
        ^^ newline ^^
        begin if import then
          nest (!^ "Import" ^^ !^ name ^-^ !^ ".") ^^ newline
        else
          empty
        end
    )) ^^ newline
  end ^^
  begin match ast.head_suffix with
  | "" -> empty
  | _ -> !^ (ast.head_suffix) ^^ newline
  end ^^
  begin match ast.content with
  | SignatureAxioms signature -> SignatureAxioms.to_coq signature
  | Structure structure -> Structure.to_coq false structure
  end ^^
  newline
