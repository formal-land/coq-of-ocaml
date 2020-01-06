open SmartPrint
open Typedtree
open Monad.Notations

type defined_or_free =
  | Defined of Type.t
  | Free

type t =
  | Error of string
  | With of PathName.t * defined_or_free Tree.t

let of_ocaml_module_with_substitutions
  (long_ident_loc : Longident.t Asttypes.loc)
  (substitutions : (Path.t * Longident.t Asttypes.loc * with_constraint) list)
  : t Monad.t =
  let signature_path_name = PathName.of_long_ident false long_ident_loc.txt in
  get_env >>= fun env ->
  let (_, module_typ) = Env.lookup_modtype long_ident_loc.txt env in
  ModuleTypParams.get_module_typ_declaration_typ_params module_typ >>= fun signature_typ_params ->
  (substitutions |> Monad.List.filter_map (fun (path, _, with_constraint) ->
    begin match with_constraint with
    | Twith_type { typ_loc; typ_type; _ } ->
      begin match typ_type with
      | { type_kind = Type_abstract; type_manifest = Some typ; _ } ->
        set_loc (Loc.of_location typ_loc) (
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return (Some (PathName.of_path_without_convert false path, typ)))
      | _ ->
        raise None NotSupported (
          "Can only do `with` on types in module types using type expressions " ^
          "rather than type definitions."
        )
      end
    | _ -> raise None NotSupported "Can only do `with` on types in module types."
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
  | Tmty_alias _ ->
    raise (Error "alias") NotSupported "Aliases in module types are not handled."
  | Tmty_functor _ ->
    raise (Error "functor") NotSupported "The application of functors in module types is not handled."
  | Tmty_ident (_, long_ident_loc) ->
    of_ocaml_module_with_substitutions long_ident_loc []
  | Tmty_signature _ ->
    raise (Error "signature") NotSupported "Anonymous definition of signatures is not handled."
  | Tmty_typeof _ ->
    raise (Error "typeof") NotSupported "The typeof in module types is not handled."
  | Tmty_with ({ mty_desc = Tmty_ident (_, long_ident_loc); _ }, substitutions) ->
    of_ocaml_module_with_substitutions long_ident_loc substitutions
  | Tmty_with _ ->
    raise
      (Error "signature")
      NotSupported
      "Operator 'with' on something else than a signature name is not handled."))

let to_coq (typ_variables_prefix : Name.t) (module_typ : t) : SmartPrint.t =
  match module_typ with
  | Error message -> !^ message
  | With (path_name, typ_values) ->
    nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ^^
    separate space (Tree.flatten typ_values |> List.map (fun (path_name, defined_or_free) ->
      match defined_or_free with
      | Defined typ -> Type.to_coq None (Some Type.Context.Apply) typ
      | Free -> Name.to_coq (ModuleTypParams.get_typ_param_name (PathName.add_prefix typ_variables_prefix path_name))
    ))
