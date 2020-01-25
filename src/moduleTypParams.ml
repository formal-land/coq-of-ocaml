open Monad.Notations

type 'a t = 'a Tree.t

type 'a mapper = Ident.t -> Types.type_declaration -> 'a Tree.item option Monad.t

(* We do not report user errors in this code as this would create duplicates
   with errors generated during the translation of the signatures themselves. *)
let rec get_signature_typ_params
  (mapper : 'a mapper) (signature : Types.signature) : 'a t Monad.t =
  let get_signature_item_typ_params
    (signature_item : Types.signature_item)
    : 'a Tree.item option Monad.t =
    match signature_item with
    | Sig_value _ -> return None
    | Sig_type (ident, type_declaration, _) -> mapper ident type_declaration
    | Sig_typext _ -> return None
    | Sig_module (ident, module_declaration, _) ->
      let name = Name.of_ident false ident in
      get_module_typ_typ_params
        mapper module_declaration.md_type >>= fun typ_params ->
      return (Some (Tree.Module (name, typ_params)))
    | Sig_modtype _ | Sig_class _ | Sig_class_type _ -> return None in
  signature |> Monad.List.filter_map get_signature_item_typ_params

and get_module_typ_typ_params
  (mapper : 'a mapper) (module_typ : Types.module_type) : 'a t Monad.t =
  match module_typ with
  | Mty_signature signature ->
    get_signature_typ_params mapper signature
  | Mty_alias (_, path) | Mty_ident path ->
    get_env >>= fun env ->
    begin match Env.find_modtype path env with
    | module_typ -> get_module_typ_declaration_typ_params mapper module_typ
    | exception Not_found -> return []
    end
  | Mty_functor _ -> return []

and get_module_typ_declaration_typ_params
  (mapper : 'a mapper) (module_typ_declaration : Types.modtype_declaration)
  : 'a t Monad.t =
  match module_typ_declaration.mtd_type with
  | None -> return []
  | Some module_typ ->
    get_module_typ_typ_params mapper module_typ

let mapper_get_arity
  (ident : Ident.t)
  (type_declaration : Types.type_declaration)
  : int Tree.item option Monad.t =
  match type_declaration.type_manifest with
  | None ->
    let name = Name.of_ident false ident in
    let arity = List.length type_declaration.type_params in
    return (Some (Tree.Item (name, arity)))
  | Some _ -> return None

let get_signature_typ_params_arity =
  get_signature_typ_params mapper_get_arity

let get_module_typ_typ_params_arity =
  get_module_typ_typ_params mapper_get_arity

let get_module_typ_declaration_typ_params_arity =
  get_module_typ_declaration_typ_params mapper_get_arity

let get_typ_param_name (path_name : PathName.t) : Name.t =
  Name.of_string
    false
    (String.concat "_" ((path_name.path @ [path_name.base]) |> List.map Name.to_string))

let get_module_typ_nb_of_existential_variables (module_typ : Types.module_type)
  : int Monad.t =
  get_module_typ_typ_params mapper_get_arity module_typ >>= fun typ_params ->
  return (Tree.size typ_params)
