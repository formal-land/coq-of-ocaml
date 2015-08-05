open SmartPrint

let exp (structure : Typedtree.structure) : Loc.t Structure.t list =
  let (_, defs) = Structure.of_structure PervasivesModule.env structure in
  snd @@ Structure.monadise_let_rec PervasivesModule.env defs

let effects (structure : Typedtree.structure)
  : (Loc.t * Effect.t) Structure.t list =
  snd @@ Structure.effects PervasivesModule.env_with_effects @@ exp structure

let monadise (structure : Typedtree.structure) : Loc.t Structure.t list =
  snd @@ Structure.monadise PervasivesModule.env @@ effects structure

let interface (structure : Typedtree.structure) (module_name : string)
  : Interface.t =
  Interface.Interface (module_name, Interface.of_structures (effects structure))

(** Display on stdout the conversion in Coq of an OCaml structure. *)
let of_ocaml (structure : Typedtree.structure) (mode : string)
  (module_name : string) : unit =
  try
    let document =
      match mode with
      | "exp" -> Structure.pps Loc.pp @@ exp structure
      | "effects" ->
        let pp_annotation (l, effect) =
          OCaml.tuple [Loc.pp l; Effect.pp effect] in
        Structure.pps pp_annotation @@ effects structure
      | "monadise" -> Structure.pps Loc.pp @@ monadise structure
      | "v" ->
        concat (List.map (fun d -> d ^^ newline) [
          !^ "Require Import OCaml.OCaml." ^^ newline;
          !^ "Local Open Scope Z_scope.";
          !^ "Local Open Scope type_scope.";
          !^ "Import ListNotations."]) ^^ newline ^^
        Structure.to_coq (monadise structure)
      | "interface" ->
        !^ (Interface.to_json_string (interface structure module_name))
      | _ -> failwith (Printf.sprintf "Unknown mode '%s'." mode) in
    to_stdout 80 2 document;
    print_newline ();
    flush stdout with
  | Error.Make x ->
    prerr_endline @@ to_string 80 2 @@ (!^ "Error:" ^^ Error.pp x)

(** Parse a .cmt file to a typed AST. *)
let parse_cmt (file_name : string) : Typedtree.structure =
  let (_, cmt) = Cmt_format.read file_name in
  match cmt with
  | Some { Cmt_format.cmt_annots = Cmt_format.Implementation structure } ->
    structure
  | _ -> failwith "Cannot extract cmt data."

let module_name (file_name : string) : string =
  String.capitalize @@ Filename.chop_extension @@ Filename.basename file_name

(** The main function. *)
let main () =
  let file_name = ref None in
  let mode = ref "" in
  let options = [
    "-mode", Arg.Set_string mode, " v (generate Coq .v files, you probably want this option), exp (the simplified expression tree), effects (the inferred effects), monadise (the expression tree after monadisation), interface (the equivalent of .mli with effects)"] in
  let usage_msg = "Usage: ./coqOfOCaml.native file.cmt\nOptions are:" in
  Arg.parse options (fun arg -> file_name := Some arg) usage_msg;
  match !file_name with
  | None -> Arg.usage options usage_msg
  | Some file_name -> of_ocaml (parse_cmt file_name) !mode (module_name file_name);

;;main ()
