open SmartPrint
open Monad.Notations

type t =
  | Error of string
  | Functor of Name.t * t * t
  | With of PathName.t * Type.arity_or_typ Tree.t

let rec get_module_typ_desc_path
  (module_typ_desc : Typedtree.module_type_desc) : Path.t option =
  match module_typ_desc with
  | Tmty_ident (path, _) -> Some path
  | Tmty_signature _ -> None
  | Tmty_functor _ -> None
  | Tmty_with (module_typ, _) -> get_module_typ_path_name module_typ
  | Tmty_typeof _ -> None
  | Tmty_alias _ -> None

and get_module_typ_path_name (module_typ : Typedtree.module_type)
  : Path.t option =
  get_module_typ_desc_path module_typ.mty_desc

let of_ocaml_module_with_substitutions
  (long_ident_loc : Longident.t Asttypes.loc)
  (substitutions :
    (Path.t * Longident.t Asttypes.loc * Typedtree.with_constraint) list)
  : t Monad.t =
  let signature_path_name = PathName.of_long_ident false long_ident_loc.txt in
  get_env >>= fun env ->
  let (_, module_typ) = Env.lookup_modtype long_ident_loc.txt env in
  ModuleTypParams.get_module_typ_declaration_typ_params_arity
    module_typ >>= fun signature_typ_params ->
  (substitutions |> Monad.List.filter_map (fun (path, _, with_constraint) ->
    begin match with_constraint with
    | Typedtree.Twith_type typ_declaration | Twith_typesubst typ_declaration ->
      let { Typedtree.typ_loc; typ_type; _ } = typ_declaration in
      begin match typ_type with
      | { type_kind = Type_abstract; type_manifest = Some typ; type_params; _ } ->
        set_loc (Loc.of_location typ_loc) (
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        Monad.List.map Type.of_type_expr_variable type_params >>= fun typ_params ->
        return (Some (PathName.of_path_without_convert false path, typ_params, typ)))
      | _ ->
        raise None NotSupported (
          "Can only do `with` on types in module types using type expressions " ^
          "rather than type definitions"
        )
      end
    | _ -> raise None NotSupported "Can only do `with` on types in module types"
    end
  )) >>= fun (typ_substitutions : (PathName.t * Name.t list * Type.t) list) ->
  let typ_values = List.fold_left
    (fun typ_values (path_name, typ_params, typ) ->
      Tree.map_at typ_values path_name (fun _ ->
        Type.Typ (Type.FunTyps (typ_params, typ))
      )
    )
    (signature_typ_params |> Tree.map (fun arity -> Type.Arity arity))
    typ_substitutions in
  return (With (signature_path_name, typ_values))

let rec of_ocaml_desc (module_typ_desc : Typedtree.module_type_desc) : t Monad.t =
  match module_typ_desc with
  | Tmty_alias _ ->
    raise (Error "alias") NotSupported "Aliases in module types are not handled"
  | Tmty_functor (ident, _, Some param, result) ->
    let name = Name.of_ident false ident in
    of_ocaml param >>= fun param ->
    of_ocaml result >>= fun result ->
    return (Functor (name, param, result))
  | Tmty_functor (_, _, None, _) ->
    raise
      (Error "generative_functor")
      NotSupported
      "Generative functors are not handled"
  | Tmty_ident (_, long_ident_loc) ->
    of_ocaml_module_with_substitutions long_ident_loc []
  | Tmty_signature _ ->
    raise
      (Error "anonymous_signature")
      NotSupported
      "Anonymous definition of signatures is not handled"
  | Tmty_typeof _ ->
    raise (Error "typeof") NotSupported "The typeof in module types is not handled"
  | Tmty_with ({ mty_desc = Tmty_ident (_, long_ident_loc); _ }, substitutions) ->
    of_ocaml_module_with_substitutions long_ident_loc substitutions
  | Tmty_with _ ->
    raise
      (Error "signature")
      NotSupported
      "Operator 'with' on something else than a signature name is not handled"

and of_ocaml (module_typ : Typedtree.module_type) : t Monad.t =
  set_env module_typ.mty_env (
  set_loc (Loc.of_location module_typ.mty_loc) (
  of_ocaml_desc module_typ.mty_desc))

let rec to_typ (module_typ : t) : Type.t =
  match module_typ with
  | Error message -> Type.Error message
  | Functor (name, param, result) ->
    Type.ForallModule (name, to_typ param, to_typ result)
  | With (path_name, typ_values) ->
    Type.Package (false, path_name, typ_values)

let to_coq (typ_variables_prefix : Name.t) (module_typ : t) : SmartPrint.t =
  match module_typ with
  | Error message -> !^ message
  | Functor _ -> Type.to_coq None None (to_typ module_typ)
  | With (path_name, typ_values) ->
    nest (
      nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ^^
      separate space (Tree.flatten typ_values |> List.map (fun (path_name, arity_or_typ) ->
        match arity_or_typ with
        | Type.Typ typ -> Type.to_coq None (Some Type.Context.Apply) typ
        | Arity _ ->
          Name.to_coq (
            ModuleTypParams.get_typ_param_name
              (PathName.add_prefix typ_variables_prefix path_name)
          )
      ))
    )
