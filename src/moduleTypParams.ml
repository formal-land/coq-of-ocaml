open Monad.Notations

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
      raise None NotSupported "Type extensions are not handled"
    | Sig_module (ident, module_declaration, _) ->
      let name = Name.of_ident ident in
      set_loc (Loc.of_location module_declaration.md_loc) (
      get_module_typ_typ_params module_declaration.md_type >>= fun typ_params ->
      return (Some (Tree.Module (name, typ_params))))
    | Sig_modtype _ ->
      raise None NotSupported "Nested signatures are not handled in signatures"
    | Sig_class _ ->
      raise None NotSupported "Classes are not handled"
    | Sig_class_type _ ->
      raise None NotSupported "Class types are not handled" in
  signature |> Monad.List.filter_map get_signature_item_typ_params

and get_module_typ_typ_params (module_typ : Types.module_type) : unit Tree.t Monad.t =
  match module_typ with
  | Mty_signature signature ->
    get_signature_typ_params signature
  | Mty_alias (_, path) | Mty_ident path ->
    get_env >>= fun env ->
    get_module_typ_declaration_typ_params (Env.find_modtype path env)
  | Mty_functor _ ->
    raise [] NotSupported "Cannot instantiate functors (yet)."

and get_module_typ_declaration_typ_params
  (module_typ_declaration : Types.modtype_declaration)
  : unit Tree.t Monad.t =
  set_loc (Loc.of_location module_typ_declaration.mtd_loc) (
  match module_typ_declaration.mtd_type with
  | None ->
    raise [] NotSupported "Cannot instantiate an abstract signature."
  | Some module_typ ->
    get_module_typ_typ_params module_typ)

let get_typ_param_name (path_name : PathName.t) : Name.t =
  Name.of_string (String.concat "_" (path_name.path @ [path_name.base]))
