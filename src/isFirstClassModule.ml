(** Utilities to check if a module is a first-class module and get the
    namespace of its signature definition. *)
open Monad.Notations

(** Recursively get all the module type declarations inside a module declaration.
    We retreive the path prefix and definition of each. *)
let rec get_modtype_declarations_of_module_declaration
  (module_declaration : Types.module_declaration)
  : (Ident.t list * Types.modtype_declaration) list =
  match module_declaration.md_type with
  | Mty_signature signature ->
    List.flatten (signature |> List.map (function
      | Types.Sig_module (module_ident, module_declaration, _) ->
        let signatures = get_modtype_declarations_of_module_declaration module_declaration in
        signatures |> List.map (fun (signature_path_prefix, signature) ->
          (module_ident :: signature_path_prefix, signature)
        )
      | Sig_modtype (_, module_type) -> [([], module_type)]
      | _ -> []
    ))
  | _ -> []

let is_modtype_declaration_similar_to_shape
  (modtype_declaration : Types.modtype_declaration)
  (shape : SignatureShape.t)
  : bool =
  match modtype_declaration.mtd_type with
  | Some (Mty_signature signature) ->
    let shape' = SignatureShape.of_signature signature in
    SignatureShape.are_equal shape shape'
  | _ -> false

let rec apply_idents_on_path (path : Path.t) (idents : Ident.t list) : Path.t =
  List.fold_left (fun path ident -> Path.Pdot (path, Ident.name ident, 0)) path (List.rev idents)

(** Find the [Path.t] of all the signature definitions which are found to be similar
    to [signature]. If the signature is the one of a module used as a namespace there
    should be none. If the signature is the one a first-class module ther should be
    exactly one. There may be more than one result if two signatures have the same
    or similar definitions. In this case we fail with an explicit error message. *)
let find_similar_signatures (env : Env.t) (signature : Types.signature) : Path.t list =
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
    Env.fold_modules
      (fun _ module_path module_declaration signature_paths ->
        let modtype_declarations = get_modtype_declarations_of_module_declaration module_declaration in
        let similar_modtype_declarations =
          modtype_declarations |> List.filter (fun (_, modtype_declaration) ->
            is_modtype_declaration_similar_to_shape modtype_declaration shape
          ) in
        (similar_modtype_declarations |> List.map (fun (idents, _) -> apply_idents_on_path module_path idents)) @
        signature_paths
      )
      None env [] in
  similar_signature_paths @ similar_signature_paths_in_modules

(** Get the path of the namespace of the signature definition of the [module_typ]
    if it is a first-class module, [None] otherwise. *)
let rec is_module_typ_first_class (module_typ : Types.module_type) : Path.t option Monad.t =
  get_env >>= fun env ->
  match module_typ with
  | Mty_alias (Mta_absent, _) -> return None
  | Mty_ident path | Mty_alias (Mta_present, path) ->
    begin match Env.find_modtype path env with
    | { mtd_type = None } -> return None
    | { mtd_type = Some module_typ } -> is_module_typ_first_class module_typ
    | exception _ -> raise NotFound ("Module signature '" ^ Path.name path ^ "' not found")
    end
  | Mty_signature signature ->
    let signature_paths = find_similar_signatures env signature in
    begin match signature_paths with
    | [] -> return None
    | [signature_path] -> return (Some signature_path)
    | _ ->
      raise FirstClassModule (
        "It is unclear which first-class module this projection is from. " ^
        "At least two similar module signatures found."
      )
    end
  | Mty_functor _ -> raise NotSupported "Functor module types are not handled (yet)"
