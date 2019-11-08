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

let of_typedtree (typedtree : Mtyper.typedtree) : t Monad.t =
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
