open Monad.Notations

type 'a mapper =
  Ident.t -> Types.type_declaration -> 'a Tree.item option Monad.t

(* We do not report user errors in this code as this would create duplicates
   with errors generated during the translation of the signatures themselves. *)
let rec get_signature_typ_params (mapper : 'a mapper)
    (signature : Types.signature) : 'a Tree.t Monad.t =
  let get_signature_item_typ_params (signature_item : Types.signature_item) :
      'a Tree.item option Monad.t =
    match signature_item with
    | Sig_value _ -> return None
    | Sig_type (ident, type_declaration, _, _) -> mapper ident type_declaration
    | Sig_typext _ -> return None
    | Sig_module (ident, _, module_declaration, _, _) ->
        get_module_typ_typ_params mapper module_declaration.md_type
        >>= fun typ_params ->
        return (Some (Tree.Module (Ident.name ident, typ_params)))
    | Sig_modtype _ | Sig_class _ | Sig_class_type _ -> return None
  in
  signature |> Monad.List.filter_map get_signature_item_typ_params

and get_module_typ_typ_params (mapper : 'a mapper)
    (module_typ : Types.module_type) : 'a Tree.t Monad.t =
  match module_typ with
  | Mty_signature signature -> get_signature_typ_params mapper signature
  | Mty_alias path | Mty_ident path -> (
      get_env >>= fun env ->
      match Env.find_modtype path env with
      | module_typ -> get_module_typ_declaration_typ_params mapper module_typ
      | exception Not_found -> return [])
  | Mty_functor _ -> return []
  | Mty_for_hole -> return []

and get_module_typ_declaration_typ_params (mapper : 'a mapper)
    (module_typ_declaration : Types.modtype_declaration) : 'a Tree.t Monad.t =
  match module_typ_declaration.mtd_type with
  | None -> return []
  | Some module_typ -> get_module_typ_typ_params mapper module_typ

let mapper_get_arity (ident : Ident.t)
    (type_declaration : Types.type_declaration) : int Tree.item option Monad.t =
  match type_declaration.type_manifest with
  | None ->
      let arity = List.length type_declaration.type_params in
      return (Some (Tree.Item (Ident.name ident, arity)))
  | Some _ -> return None

let get_signature_typ_params_arity = get_signature_typ_params mapper_get_arity
let get_module_typ_typ_params_arity = get_module_typ_typ_params mapper_get_arity

let get_module_typ_declaration_typ_params_arity =
  get_module_typ_declaration_typ_params mapper_get_arity

(** The number of abstract types in a functor's parameters. *)
let rec get_functor_nb_free_vars_params (module_typ : Types.module_type) :
    int Monad.t =
  match module_typ with
  | Mty_functor (param, module_typ) ->
      let* param_free_vars_arities =
        match param with
        | Unit -> return []
        | Named (_, param) -> get_module_typ_typ_params_arity param
      in
      let nb_free_vars_param =
        param_free_vars_arities |> Tree.flatten |> List.length
      in
      let* nb_free_vars_module_typ =
        get_functor_nb_free_vars_params module_typ
      in
      return (nb_free_vars_param + nb_free_vars_module_typ)
  | _ -> return 0
