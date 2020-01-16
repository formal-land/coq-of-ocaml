(** Utilities to check if a module is a first-class module and get the
    namespace of its signature definition. *)
open Monad.Notations

(** Recursively get all the module type declarations inside a module declaration.
    We retreive the path and definition of each. *)
let get_modtype_declarations_of_module_declaration
  (module_declaration : Types.module_declaration)
  : (Ident.t list * Types.modtype_declaration) list =
  match module_declaration.md_type with
  | Mty_signature signature ->
    signature |> Util.List.filter_map (function
      | Types.Sig_modtype (module_type_ident, module_type) ->
        Some ([module_type_ident], module_type)
      | _ -> None
    )
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

let apply_idents_on_path (path : Path.t) (idents : Ident.t list) : Path.t =
  List.fold_left (fun path ident ->
    Path.Pdot (path, Ident.name ident, 0)
  ) path idents

(** Find the [Path.t] of all the signature definitions which are found to be similar
    to [signature]. If the signature is the one of a module used as a namespace there
    should be none. If the signature is the one a first-class module there should be
    exactly one. There may be more than one result if two signatures have the same
    or similar definitions. In this case we will fail later with an explicit
    error message. *)
let find_similar_signatures (env : Env.t) (signature : Types.signature)
  : Path.t list * unit Tree.t =
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
        (similar_modtype_declarations |> List.map (fun (idents, _) ->
          apply_idents_on_path module_path idents
        )) @ signature_paths
      )
      None env [] in
  (similar_signature_paths @ similar_signature_paths_in_modules, shape)

type maybe_found =
  | Found of Path.t
  | Not_found of string option

(** Get the path of the signature definition of the [module_typ]
    if it is a first-class module, [None] otherwise. *)
let is_module_typ_first_class
  (module_typ : Types.module_type)
  : maybe_found Monad.t =
  get_env >>= fun env ->
  match Mtype.scrape env module_typ with
  | Mty_alias _ | Mty_ident _ -> return (Not_found None)
  | Mty_signature signature ->
    let (signature_paths, shape) = find_similar_signatures env signature in
    begin match signature_paths with
    | [] ->
      return (
        Not_found (
          Some (
            "Did not find a module signature name for the following shape:\n" ^
            Pp.to_string (SignatureShape.pretty_print shape) ^ "\n" ^
            "(a shape is a list of names of values)\n\n" ^
            "We use the concept of shape to find the name of a signature for Coq."
          )
        )
      )
    | [signature_path] -> return (Found signature_path)
    | signature_path :: (_ :: _) ->
      raise (Found signature_path) FirstClassModule (
        "It is unclear which first-class module this projection is from. At least two similar\n" ^
        "module signatures found, namely:\n" ^
        String.concat ", " (signature_paths |> List.map Path.name) ^ "\n\n" ^
        "We were looking for a module signature name for the following shape:\n" ^
        Pp.to_string (SignatureShape.pretty_print shape) ^ "\n" ^
        "(a shape is a list of names of values)\n\n" ^
        "We use the concept of shape to find the name of a signature for Coq."
      )
    end
  | Mty_functor _ -> return (Not_found (Some "This is a functor type."))
