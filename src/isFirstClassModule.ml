(** Utilities to check if a module is a first-class module and get the
    namespace of its signature definition. *)
open Monad.Notations

(** Recursively get all the module type declarations inside a module declaration.
    We retreive the path and definition of each. *)
let get_modtype_declarations_of_module_declaration
  (env : Env.t) (module_declaration : Types.module_declaration)
  : (Ident.t list * Types.modtype_declaration) list =
  match Env.scrape_alias env module_declaration.md_type with
  | Mty_signature signature ->
    signature |> Util.List.filter_map (function
      | Types.Sig_modtype (module_type_ident, module_type, _) ->
        Some ([module_type_ident], module_type)
      | _ -> None
    )
  | _ -> []
  | exception _ -> []

let is_modtype_declaration_similar_to_shape
  (modtype_declaration : Types.modtype_declaration)
  (shape : SignatureShape.t)
  : bool =
  match modtype_declaration.mtd_type with
  | Some (Mty_signature signature) ->
    let shape' = SignatureShape.of_signature signature in
    SignatureShape.are_equal shape shape'
  | _ -> false

let apply_idents_on_path (path : Path.t) (idents : Ident.t list) : Path.t =
  List.fold_left (fun path ident ->
    Path.Pdot (path, Ident.name ident)
  ) path idents

let is_black_list (path : Path.t) : bool =
  match PathName.of_path_without_convert false path with
  | _ -> false

let merge_similar_paths (paths : Path.t list) : Path.t list =
  paths |> List.sort_uniq PathName.compare_paths

(** Find the [Path.t] of all the signature definitions which are found to be similar
    to [signature]. If the signature is the one of a module used as a namespace there
    should be none. If the signature is the one a first-class module there should be
    exactly one. There may be more than one result if two signatures have the same
    or similar definitions. In this case we will fail later with an explicit
    error message. *)
let find_similar_signatures (env : Env.t) (signature : Types.signature)
  : Path.t list * SignatureShape.t =
  let shape = SignatureShape.of_signature signature in
  (* We explore signatures in the current namespace. *)
  let similar_signature_paths =
    Env.fold_modtypes
      (fun _ signature_path modtype_declaration signature_paths ->
        if is_modtype_declaration_similar_to_shape modtype_declaration shape then
          signature_path :: signature_paths
        else
          signature_paths
      )
      None env [] in
  (* We explore signatures in modules in the current namespace. *)
  let similar_signature_paths_in_modules =
    (* We favor locally defined signatures. *)
    match similar_signature_paths with
    | _ :: _ -> []
    | [] ->
      Env.fold_modules
        (fun _ module_path module_declaration signature_paths ->
          let similar_modtype_declarations =
            get_modtype_declarations_of_module_declaration
              env module_declaration |>
            List.filter (fun (_, modtype_declaration) ->
              is_modtype_declaration_similar_to_shape modtype_declaration shape
            ) |>
            List.map (fun (idents, _) ->
              apply_idents_on_path module_path idents
            ) in
          similar_modtype_declarations @ signature_paths
        )
        None env [] in
  let paths =
    (similar_signature_paths @ similar_signature_paths_in_modules) |>
    merge_similar_paths |>
    List.filter (fun path -> not (is_black_list path)) in
  (paths, shape)

type maybe_found =
  | Found of Path.t
  | Not_found of string

(** Get the path of the signature definition of the [module_typ]
    if it is a first-class module, [None] otherwise. *)
let rec is_module_typ_first_class
  (module_typ : Types.module_type)
  : maybe_found Monad.t =
  get_env >>= fun env ->
  match Mtype.scrape env module_typ with
  | Mty_alias path | Mty_ident path ->
    begin match Env.find_module path env with
    | { Types.md_type; _ } -> is_module_typ_first_class md_type
    | exception Not_found ->
      let reason = "Module " ^ Path.name path ^ " not found" in
      return (Not_found reason)
    end
  | Mty_signature signature ->
    let (signature_paths, shape) = find_similar_signatures env signature in
    begin match signature_paths with
    | [] ->
      return (
        Not_found (
          "Did not find a module signature name for the following shape:\n" ^
          Pp.to_string (SignatureShape.pretty_print shape) ^ "\n" ^
          "(a shape is a list of names of values and sub-modules)\n\n" ^
          "We use the concept of shape to find the name of a signature for Coq."
        )
      )
    | [signature_path] -> return (Found signature_path)
    | signature_path :: (_ :: _) ->
      raise (Found signature_path) FirstClassModule (
        "It is unclear which name has this signature. At least two similar\n" ^
        "signatures found, namely:\n" ^
        String.concat ", " (signature_paths |> List.map Path.name) ^ "\n\n" ^
        "We were looking for a module signature name for the following shape:\n" ^
        Pp.to_string (SignatureShape.pretty_print shape) ^ "\n" ^
        "(a shape is a list of names of values and sub-modules)\n\n" ^
        "We use the concept of shape to find the name of a signature for Coq."
      )
    end
  | Mty_functor _ -> return (Not_found "This is a functor type.")
