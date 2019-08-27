(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open Typedtree
open Sexplib.Std
open SmartPrint

type t =
  | Access of t * PathName.t
  | PathName of PathName.t
  [@@deriving sexp]

let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

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

let find_similar_signatures (env : Env.t) (signature : Types.signature) : Path.t list =
  let shape = SignatureShape.of_signature signature in
  let similar_signature_paths =
    Env.fold_modtypes
      (fun _ signature_path modtype_declaration signature_paths ->
        if is_modtype_declaration_similar_to_shape modtype_declaration shape then
          signature_path :: signature_paths
        else
          signature_paths
      )
      None env [] in
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

let rec of_path_aux (env : Env.t) (loc : Loc.t) (path : Path.t) : Path.t * (Path.t * string) list =
  match path with
  | Papply _ -> Error.raise loc "Application of paths is not handled"
  | Pdot (path, field_string, pos) ->
    let (path, fields) = of_path_aux env loc path in
    begin match fields with
    | [] ->
      begin match Env.find_module path env with
      | module_declaration ->
      begin match module_declaration.md_type with
      | Mty_signature signature ->
          let signature_paths = find_similar_signatures env signature in
          begin match signature_paths with
          | [] -> (Pdot (path, field_string, pos), [])
          | [signature_path] ->
            (path, [(signature_path, field_string)])
          | _ ->
            Error.raise loc (
              "It is unclear which first-class module this projection is from. " ^
              "At least two similar module signatures."
            )
          end
        | _ -> Error.raise loc "Unhandled kind of module signature for this module"
        end
      | exception _ -> Error.raise loc "Unexpected module not found"
      end
    | _ :: _ -> Error.raise loc "Does not handled nested accesses into first-class modules (yet)"
    end
  | Pident _ -> (path, [])

let of_path (env : Env.t) (loc : Loc.t) (path : Path.t) : t =
  let (path, fields) = of_path_aux env loc path in
  let path_name = PathName.of_path loc path in
  List.fold_left
    (fun mixed_path (signature_path, field_string) ->
      let field_path_name = PathName.of_path loc (Pdot (signature_path, field_string, 0)) in
      Access (mixed_path, field_path_name))
    (PathName path_name)
    (List.rev fields)

let rec to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, field_path_name) ->
    parens (!^ "projT2" ^^ to_coq path) ^-^ !^ "." ^-^ parens (PathName.to_coq field_path_name)
  | PathName path_name -> PathName.to_coq path_name
