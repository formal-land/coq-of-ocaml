open Monad.Notations
(** Utilities to check if a module is a first-class module and get the
    namespace of its signature definition. *)

(** Recursively get all the module type declarations inside a module declaration.
    We retreive the path and definition of each. *)
let rec get_modtype_declarations_of_module_declaration (env : Env.t)
    (module_declaration : Types.module_declaration) :
    (Ident.t list * Types.modtype_declaration) list =
  match Env.scrape_alias env module_declaration.md_type with
  | Mty_signature signature ->
      signature
      |> List.concat_map (function
           | Types.Sig_modtype (module_type_ident, module_type, _) ->
               [ ([ module_type_ident ], module_type) ]
           | Sig_module (ident, _, module_declaration, _, _) ->
               get_modtype_declarations_of_module_declaration env
                 module_declaration
               |> List.map (fun (idents, declaration) ->
                      (ident :: idents, declaration))
           | _ -> [])
  | _ -> []
  | exception _ -> []

let is_modtype_declaration_similar_to_shape (env : Env.t)
    (modtype_declaration : Types.modtype_declaration) (shape : SignatureShape.t)
    : bool =
  match Option.map (Env.scrape_alias env) modtype_declaration.mtd_type with
  | Some (Mty_signature signature) ->
      let shape' =
        SignatureShape.of_signature (Some modtype_declaration.mtd_attributes)
          signature
      in
      SignatureShape.are_equal shape shape'
  | _ -> false

let apply_idents_on_path (path : Path.t) (idents : Ident.t list) : Path.t =
  List.fold_left
    (fun path ident -> Path.Pdot (path, Ident.name ident))
    path idents

let merge_similar_paths (paths : Path.t list) : Path.t list Monad.t =
  paths |> Monad.List.sort_uniq PathName.compare_paths

let find_similar_signatures_with_shape (env : Env.t) (shape : SignatureShape.t)
    : (Path.t list * SignatureShape.t) Monad.t =
  (* We explore signatures in the current namespace. *)
  let similar_signature_paths =
    Env.fold_modtypes
      (fun _ signature_path modtype_declaration signature_paths ->
        if is_modtype_declaration_similar_to_shape env modtype_declaration shape
        then signature_path :: signature_paths
        else signature_paths)
      None env []
  in
  (* We explore signatures in modules in the current namespace. *)
  let similar_signature_paths_in_modules =
    (* We favor locally defined signatures. *)
    match similar_signature_paths with
    | _ :: _ -> []
    | [] ->
        Env.fold_modules
          (fun _ module_path module_declaration signature_paths ->
            let similar_modtype_declarations =
              get_modtype_declarations_of_module_declaration env
                module_declaration
              |> List.filter (fun (_, modtype_declaration) ->
                     is_modtype_declaration_similar_to_shape env
                       modtype_declaration shape)
              |> List.map (fun (idents, _) ->
                     apply_idents_on_path module_path idents)
            in
            similar_modtype_declarations @ signature_paths)
          None env []
  in
  merge_similar_paths
    (similar_signature_paths @ similar_signature_paths_in_modules)
  >>= fun paths ->
  let* paths =
    paths
    |> Monad.List.filter (fun path ->
           let* configuration = get_configuration in
           let is_in_black_list =
             Configuration.is_in_first_class_module_signature_backlist
               configuration path
           in
           return (not is_in_black_list))
  in
  return (paths, shape)

(** Find the [Path.t] of all the signature definitions which are found to be similar
    to [signature]. If the signature is the one of a module used as a namespace there
    should be none. If the signature is the one a first-class module there should be
    exactly one. There may be more than one result if two signatures have the same
    or similar definitions. In this case we will fail later with an explicit
    error message. *)
let find_similar_signatures (env : Env.t) (signature : Types.signature) :
    (Path.t list * SignatureShape.t) Monad.t =
  let shape = SignatureShape.of_signature None signature in
  if SignatureShape.is_empty shape then return ([], shape)
  else find_similar_signatures_with_shape env shape

type maybe_found = Found of Path.t | Not_found of string

(** Get the path of the signature definition of the [module_typ]
    if it is a first-class module, [None] otherwise. Optionally, when given the path of the module we want to check for its signature, to verify if it is not
    in a blacklist. *)
let rec is_module_typ_first_class_aux (module_typ : Types.module_type)
    (module_path : Path.t option) : maybe_found Monad.t =
  let* env = get_env in
  let* configuration = get_configuration in
  let* is_in_black_list =
    match module_path with
    | None -> return false
    | Some module_path ->
        let is_in_configuration_black_list =
          Configuration.is_in_first_class_module_path_backlist configuration
            module_path
        in
        let* has_black_list_attribute =
          match Env.find_module module_path env with
          | { Types.md_attributes; _ } ->
              let* attributes = Attribute.of_attributes md_attributes in
              return (Attribute.has_plain_module attributes)
          | exception _ -> return false
        in
        return (is_in_configuration_black_list || has_black_list_attribute)
  in
  if is_in_black_list then return (Not_found "In blacklist")
  else
    match Mtype.scrape env module_typ with
    | Mty_alias path | Mty_ident path -> (
        match Env.find_module path env with
        | { Types.md_type; _ } ->
            is_module_typ_first_class_aux md_type module_path
        | exception Not_found ->
            let reason = "Module " ^ Path.name path ^ " not found" in
            return (Not_found reason))
    | Mty_signature signature -> (
        find_similar_signatures env signature
        >>= fun (signature_paths, shape) ->
        match signature_paths with
        | [] ->
            return
              (Not_found
                 ("Did not find a module signature name for the following shape:\n"
                 ^ Pp.to_string (SignatureShape.pretty_print shape)
                 ^ "\n"
                 ^ "(a shape is a list of names of values and sub-modules)\n\n"
                 ^ "We use the concept of shape to find the name of a \
                    signature for Coq."))
        | [ signature_path ] -> return (Found signature_path)
        | signature_path :: _ :: _ ->
            raise (Found signature_path) Module
              ("It is unclear which name this signature has. At least two \
                similar\n" ^ "signatures found, namely:\n\n"
              ^ String.concat "\n"
                  (signature_paths
                  |> List.map (fun path -> "* " ^ Path.name path))
              ^ "\n\n"
              ^ "We were looking for a module signature name for the following \
                 shape:\n"
              ^ Pp.to_string (SignatureShape.pretty_print shape)
              ^ "\n"
              ^ "(a shape is a list of names of values and sub-modules)\n\n"
              ^ "We use the concept of shape to find the name of a signature \
                 for Coq."))
    | Mty_functor _ -> return (Not_found "This is a functor type")
    | Mty_for_hole -> return (Not_found "Module type hole")

type hash_index = {
  module_typ_shape : SignatureShape.t;
  module_path : Path.t option;
}

(** A hash to optimize the execution of the [is_module_typ_first_class]
    function. *)
module Hash = Hashtbl.Make (struct
  type t = hash_index

  let equal = ( = )
  let hash = Hashtbl.hash
end)

(** Hash having modules types for which we are sure that they have no names. *)
let not_module_typ_first_class_hash : string Hash.t = Hash.create 12

let is_module_typ_first_class (module_typ : Types.module_type)
    (module_path : Path.t option) : maybe_found Monad.t =
  let* env = get_env in
  let index =
    match module_typ with
    | Mty_signature signature ->
        let module_typ_shape = SignatureShape.of_signature None signature in
        Some { module_typ_shape; module_path }
    | _ -> None
  in
  match index with
  | Some index -> (
      match Hash.find_opt not_module_typ_first_class_hash index with
      | Some reason -> return (Not_found reason)
      | None ->
          let* result = is_module_typ_first_class_aux module_typ module_path in
          (match result with
          | Not_found reason ->
              Hash.add not_module_typ_first_class_hash index reason
          | Found _ -> ());
          return result)
  | _ -> is_module_typ_first_class_aux module_typ module_path
