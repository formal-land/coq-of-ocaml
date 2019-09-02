open Sexplib.Std
open SmartPrint
open Typedtree
open Monad.Notations

type defined_or_free =
  | Defined of Type.t
  | Free
  [@@deriving sexp]

type t =
  | With of PathName.t * defined_or_free Tree.t
  [@@deriving sexp]

let rec get_signature_typ_params (signature : Types.signature) : unit Tree.t Monad.t =
  let get_signature_item_typ_params
    (signature_item : Types.signature_item)
    : unit Tree.item option Monad.t =
    match signature_item with
    | Sig_value _ -> return None
    | Sig_type (ident, { type_manifest }, _) ->
      begin match type_manifest with
      | None ->
        let name = Name.of_ident ident in
        return (Some (Tree.Item (name, ())))
      | Some _ -> return None
      end
    | Sig_typext _ ->
      raise NotSupported "Type extensions are not handled"
    | Sig_module (ident, module_declaration, _) ->
      let name = Name.of_ident ident in
      set_loc (Loc.of_location module_declaration.md_loc) (
      get_module_typ_typ_params module_declaration.md_type >>= fun typ_params ->
      return (Some (Tree.Module (name, typ_params))))
    | Sig_modtype _ ->
      raise NotSupported "Nested signatures are not handled in signatures"
    | Sig_class _ ->
      raise NotSupported "Classes are not handled"
    | Sig_class_type _ ->
      raise NotSupported "Class types are not handled" in
  signature |> Monad.List.filter_map get_signature_item_typ_params

and get_module_typ_typ_params (module_typ : Types.module_type) : unit Tree.t Monad.t =
  match module_typ with
  | Mty_signature signature ->
    get_signature_typ_params signature
  | Mty_alias (_, path) | Mty_ident path ->
    get_env >>= fun env ->
    get_module_typ_declaration_typ_params (Env.find_modtype path env)
  | Mty_functor _ ->
    raise NotSupported "Cannot instantiate functors (yet)."

and get_module_typ_declaration_typ_params
  (module_typ_declaration : Types.modtype_declaration)
  : unit Tree.t Monad.t =
  set_loc (Loc.of_location module_typ_declaration.mtd_loc) (
  match module_typ_declaration.mtd_type with
  | None ->
    raise NotSupported "Cannot instantiate an abstract signature."
  | Some module_typ ->
    get_module_typ_typ_params module_typ)

let of_ocaml_module_with_substitutions
  (long_ident_loc : Longident.t Asttypes.loc)
  (substitutions : (Path.t * Longident.t Asttypes.loc * with_constraint) list)
  : t Monad.t =
  let signature_path_name = PathName.of_loc long_ident_loc in
  get_env >>= fun env ->
  let (_, module_typ) = Env.lookup_modtype long_ident_loc.txt env in
  get_module_typ_declaration_typ_params module_typ >>= fun signature_typ_params ->
  (substitutions |> Monad.List.map (fun (path, _, with_constraint) ->
    begin match with_constraint with
    | Twith_type { typ_loc; typ_type } ->
      begin match typ_type with
      | { type_kind = Type_abstract; type_manifest = Some typ } ->
        set_loc (Loc.of_location typ_loc) (
        Type.of_type_expr typ >>= fun typ ->
        return (PathName.of_path path, typ))
      | _ ->
        raise NotSupported (
          "Can only do `with` on types in module types using type expressions " ^
          "rather than type definitions."
        )
      end
    | _ -> raise NotSupported "Can only do `with` on types in module types."
    end
  )) >>= fun (typ_substitutions : (PathName.t * Type.t) list) ->
  let typ_values = List.fold_left
    (fun typ_values (path_name, typ) ->
      Tree.map_at typ_values path_name (fun _ -> Defined typ)
    )
    (signature_typ_params |> Tree.map (fun _ -> Free))
    typ_substitutions in
  return (With (signature_path_name, typ_values))

let of_ocaml (module_typ : module_type) : t Monad.t =
  set_env module_typ.mty_env (
  set_loc (Loc.of_location module_typ.mty_loc) (
  match module_typ.mty_desc with
  | Tmty_alias _ -> raise NotSupported "Aliases in module types are not handled."
  | Tmty_functor _ -> raise NotSupported "The application of functors in module types is not handled."
  | Tmty_ident (_, long_ident_loc) ->
    of_ocaml_module_with_substitutions long_ident_loc []
  | Tmty_signature signature ->
    raise NotSupported "Anonymous definition of signatures is not handled."
  | Tmty_typeof _ -> raise NotSupported "The typeof in module types is not handled."
  | Tmty_with ({ mty_desc = Tmty_ident (_, long_ident_loc) }, substitutions) ->
    of_ocaml_module_with_substitutions long_ident_loc substitutions
  | Tmty_with _ ->
    raise NotSupported "Operator 'with' on something else than a signature name is not handled."))

let get_typ_param_name (path_name : PathName.t) : Name.t =
  Name.of_string (String.concat "_" (path_name.path @ [path_name.base]))

let to_coq (typ_variables_prefix : Name.t) (module_typ : t) : SmartPrint.t =
  match module_typ with
  | With (path_name, typ_values) ->
    PathName.to_coq path_name ^^
    separate space (Tree.flatten typ_values |> List.map (fun (path_name, defined_or_free) ->
      match defined_or_free with
      | Defined typ -> Type.to_coq true typ
      | Free -> Name.to_coq (get_typ_param_name (PathName.add_prefix typ_variables_prefix path_name))
    ))
