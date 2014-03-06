open SmartPrint

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string) : unit =
  let env_typs : Common.env_units = PervasivesModule.env_typs in
  let env_effects : Common.env_effects = PervasivesModule.env_effects in
  let document =
    match mode with
    | "exp" ->
      let (_, defs) = Structure.of_structure env_typs structure in
      let defs = Structure.monadise_let_rec defs in
      Structure.pp OCaml.unit Loc.pp defs
    | "effects" ->
      let (_, defs) = Structure.of_structure env_typs structure in
      let defs = Structure.monadise_let_rec defs in
      let (_, defs) = Structure.effects env_effects defs in
      let pp_annotation (l, effect) =
        OCaml.tuple [Loc.pp l; Effect.pp effect] in
      Structure.pp (Effect.Type.pp false) pp_annotation defs
    | "monadise" ->
      let (_, defs) = Structure.of_structure env_typs structure in
      let defs = Structure.monadise_let_rec defs in
      let (_, defs) = Structure.effects env_effects defs in
      let (_, defs) =
        Structure.monadise PathName.Env.empty defs in
      Structure.pp OCaml.unit Loc.pp defs
    | "v" ->
      let (_, defs) = Structure.of_structure env_typs structure in
      let defs = Structure.monadise_let_rec defs in
      let (_, defs) = Structure.effects env_effects defs in
      let (_, defs) =
        Structure.monadise PathName.Env.empty defs in
      concat (List.map (fun d -> d ^^ newline) [
        !^ "Require Import CoqOfOCaml." ^^ newline;
        !^ "Local Open Scope Z_scope.";
        !^ "Import ListNotations.";
        !^ "Set Implicit Arguments."]) ^^ newline ^^
      Structure.to_coq defs
    | _ -> failwith (Printf.sprintf "Unknown mode '%s'." mode) in
  to_stdout 80 2 document;
  print_newline ();
  flush stdout

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } -> structure
  | _ -> failwith "Cannot extract cmt data."

(** The main function. *)
let main () =
  let file_name = ref None in
  let mode = ref "" in
  let options = [
    "-mode", Arg.Set_string mode, " exp, coq"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name) !mode;
  (*print_newline ();
  to_stdout 80 2 @@ Structure.pp [PervasivesModule.pervasives]*)

;;main ()