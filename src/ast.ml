(** The AST of a [.ml] or [.mli]. *)
open SmartPrint
open Monad.Notations

type t =
  | SignatureAxioms of SignatureAxioms.t
  | Structure of Structure.t list

let get_initial_loc (typedtree : Mtyper.typedtree) : Loc.t =
  match typedtree with
  | `Implementation structure ->
    begin match structure.str_items with
    | structure_item :: _ -> Loc.of_location structure_item.str_loc
    | [] -> failwith "Unexpected empty file"
    end
  | `Interface signature ->
    begin match signature.sig_items with
    | signature_item :: _ -> Loc.of_location signature_item.sig_loc
    | [] -> failwith "Unexpected empty file"
    end

let report_errors (typedtree_errors : exn list) : unit Monad.t =
  typedtree_errors |> Monad.List.iter (fun exn ->
    let error = Location.error_of_exn exn in
    match error with
    | Some (`Ok error) ->
      let loc = Location.loc_of_report error in
      let error_buffer = Buffer.create 0 in
      Location.report_error (Format.formatter_of_buffer error_buffer) error;
      set_loc (Loc.of_location loc) (raise () Error.Category.OCaml (Buffer.contents error_buffer))
    | _ -> return ()
  )

let of_typedtree (typedtree : Mtyper.typedtree) (typedtree_errors : exn list) : t Monad.t =
  report_errors typedtree_errors >>
  match typedtree with
  | `Implementation structure ->
    Structure.of_structure structure >>= fun structure ->
    return (Structure structure)
  | `Interface signature ->
    SignatureAxioms.of_signature signature >>= fun signature ->
    return (SignatureAxioms signature)

let to_coq (ast : t) : SmartPrint.t =
  concat (List.map (fun d -> d ^^ newline) [
    !^ "Require Import OCaml.OCaml." ^^ newline;
    !^ "Local Open Scope Z_scope.";
    !^ "Local Open Scope type_scope.";
    !^ "Import ListNotations."
  ]) ^^ newline ^^
  (match ast with
  | SignatureAxioms signature -> SignatureAxioms.to_coq signature
  | Structure structure -> Structure.to_coq structure) ^^
  newline