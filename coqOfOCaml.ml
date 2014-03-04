open SmartPrint

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string) : unit =
  let env_atoms : Effect.Atom.t PathName.Env.t = PervasivesModule.env_atoms in
  let env_effects : Effect.Type.t PathName.Env.t = PervasivesModule.env_effects in
  let document =
    match mode with
    | "exp" ->
      let definitions =
        Structure.monadise_let_rec (Structure.of_structure structure) in
      Structure.pp OCaml.unit Loc.pp definitions
    | "effects" ->
      let definitions =
        Structure.monadise_let_rec (Structure.of_structure structure) in
      let (_, _, definitions) =
        Structure.effects env_atoms env_effects definitions in
      let pp_annotation (l, effect) =
        OCaml.tuple [Loc.pp l; Effect.pp effect] in
      Structure.pp (Effect.Type.pp false) pp_annotation definitions
    | "monadise" ->
      let definitions =
        Structure.monadise_let_rec (Structure.of_structure structure) in
      let (_, _, definitions) =
        Structure.effects env_atoms env_effects definitions in
      let (_, definitions) =
        Structure.monadise PathName.Env.empty definitions in
      Structure.pp OCaml.unit Loc.pp definitions
    | "v" ->
      let definitions =
        Structure.monadise_let_rec (Structure.of_structure structure) in
      let (_, _, definitions) =
        Structure.effects env_atoms env_effects definitions in
      let (_, definitions) =
        Structure.monadise PathName.Env.empty definitions in
      concat (List.map (fun d -> d ^^ newline) [
        !^ "Require Import CoqOfOCaml." ^^ newline;
        !^ "Local Open Scope Z_scope.";
        !^ "Import ListNotations.";
        !^ "Set Implicit Arguments."]) ^^ newline ^^
      Structure.to_coq definitions
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