open SmartPrint
open Monad.Notations

type free_var = { name : Name.t; arity : int; source_name : Name.t }
type free_vars = free_var list

let to_coq_grouped_free_vars (free_vars : free_vars) : SmartPrint.t =
  free_vars
  |> List.map (fun { name; arity; _ } -> (name, arity))
  |> Type.to_coq_grouped_typ_params Type.Braces

module Module = struct
  type t = Error of string | With of PathName.t * Type.arity_or_typ Tree.t

  (** Return a type together with the list of its free variables with arity. We
      prefix the names of the free variables by the module name. *)
  let to_typ (functor_params : Name.t list) (module_name : string)
      (with_implicits : bool) (module_typ : t) : (free_vars * Type.t) Monad.t =
    match module_typ with
    | Error message -> return ([], Type.Error message)
    | With (path_name, typ_values) ->
        let typ_values = Tree.flatten typ_values in
        let* free_vars =
          if with_implicits then return []
          else
            typ_values
            |> Monad.List.filter_map (fun (path, arity_or_typ) ->
                   match arity_or_typ with
                   | Type.Arity arity ->
                       let* name =
                         Name.of_strings false (module_name :: path)
                       in
                       let* source_name = Name.of_strings false path in
                       return (Some { name; arity; source_name })
                   | _ -> return None)
        in
        let* typ_params =
          typ_values
          |> Monad.List.map (fun (path, arity_or_typ) ->
                 let* param_name = Name.of_strings false path in
                 match arity_or_typ with
                 | Type.Arity _ ->
                     if with_implicits then return (param_name, None)
                     else
                       let* name =
                         Name.of_strings false (module_name :: path)
                       in
                       let functor_params =
                         functor_params
                         |> List.map (fun name -> Type.Variable name)
                       in
                       let typs =
                         List.combine functor_params
                           (Type.tag_no_args functor_params)
                       in
                       let typ = Type.Apply (MixedPath.of_name name, typs) in
                       return (param_name, Some typ)
                 | Typ typ -> return (param_name, Some typ))
        in
        return (free_vars, Type.Signature (path_name, typ_params))
end

type t = (string * Module.t) list * Module.t

let rec get_module_typ_desc_path (module_typ_desc : Typedtree.module_type_desc)
    : Path.t option =
  match module_typ_desc with
  | Tmty_ident (path, _) -> Some path
  | Tmty_signature _ -> None
  | Tmty_functor _ -> None
  | Tmty_with (module_typ, _) -> get_module_typ_path_name module_typ
  | Tmty_typeof _ -> None
  | Tmty_alias _ -> None

and get_module_typ_path_name (module_typ : Typedtree.module_type) :
    Path.t option =
  get_module_typ_desc_path module_typ.mty_desc

let of_ocaml_module_with_substitutions (signature_path : Path.t)
    (substitutions :
      (Path.t * Longident.t Asttypes.loc * Typedtree.with_constraint) list) :
    Module.t Monad.t =
  let* signature_path_name =
    PathName.of_path_with_convert false signature_path
  in
  let* env = get_env in
  let module_typ = Env.find_modtype signature_path env in
  ModuleTypParams.get_module_typ_declaration_typ_params_arity module_typ
  >>= fun signature_typ_params ->
  substitutions
  |> Monad.List.filter_map
       (fun (_, { Asttypes.txt = long_ident; _ }, with_constraint) ->
         match with_constraint with
         | Typedtree.Twith_type typ_declaration
         | Twith_typesubst typ_declaration -> (
             let { Typedtree.typ_loc; typ_type; _ } = typ_declaration in
             match typ_type with
             | {
              type_kind = Type_abstract;
              type_manifest = Some typ;
              type_params;
              _;
             } ->
                 set_loc typ_loc
                   ( Type.of_type_expr_without_free_vars typ >>= fun typ ->
                     Monad.List.map Type.of_type_expr_variable type_params
                     >>= fun typ_params ->
                     let path = Longident.flatten long_ident in
                     return (Some (path, typ_params, typ)) )
             | _ ->
                 raise None NotSupported
                   ("Can only do `with` on types in module types using type \
                     expressions " ^ "rather than type definitions"))
         | _ ->
             raise None NotSupported
               "Can only do `with` on types in module types")
  >>= fun (typ_substitutions : (string list * Name.t list * Type.t) list) ->
  let typ_values =
    List.fold_left
      (fun typ_values (path, typ_params, typ) ->
        Tree.map_at typ_values path (fun _ ->
            Type.Typ (Type.FunTyps (typ_params, typ))))
      (signature_typ_params |> Tree.map (fun arity -> Type.Arity arity))
      typ_substitutions
  in
  return (Module.With (signature_path_name, typ_values))

let rec of_ocaml_desc (module_typ_desc : Typedtree.module_type_desc) : t Monad.t
    =
  match module_typ_desc with
  | Tmty_alias _ ->
      raise ([], Module.Error "alias") NotSupported
        "Aliases in module types are not handled"
  | Tmty_functor (Named (ident, _, param), result) ->
      let id = Name.string_of_optional_ident ident in
      let* params_of_param, param = of_ocaml param in
      let* params, result = of_ocaml result in
      let* param =
        match params_of_param with
        | [] -> return param
        | _ :: _ ->
            raise (Module.Error "functor_parameter") NotSupported
              ("Functors as functor parameters are not supported.\n\n"
             ^ "You can encapsulated it into a signature with this functor "
             ^ "as a field.")
      in
      return ((id, param) :: params, result)
  | Tmty_functor (Unit, _) ->
      raise
        ([], Module.Error "generative_functor")
        NotSupported "Generative functors are not handled"
  | Tmty_ident (path, _) ->
      let* modul = of_ocaml_module_with_substitutions path [] in
      return ([], modul)
  | Tmty_signature _ ->
      raise
        ([], Module.Error "anonymous_signature")
        NotSupported "Anonymous definition of signatures is not handled"
  | Tmty_typeof _ ->
      raise
        ([], Module.Error "typeof")
        NotSupported "The typeof in module types is not handled"
  | Tmty_with ({ mty_desc = Tmty_ident (path, _); _ }, substitutions) ->
      let* modul = of_ocaml_module_with_substitutions path substitutions in
      return ([], modul)
  | Tmty_with _ ->
      raise
        ([], Module.Error "signature")
        NotSupported
        "Operator 'with' on something else than a signature name is not handled"

and of_ocaml (module_typ : Typedtree.module_type) : t Monad.t =
  set_env module_typ.mty_env
    (set_loc module_typ.mty_loc (of_ocaml_desc module_typ.mty_desc))

let to_typ (functor_params : Name.t list) (module_name : string)
    (with_implicits : bool) (module_typ : t) :
    ((free_vars * (Name.t * Type.t) list * free_vars) * Type.t) Monad.t =
  let params, result = module_typ in
  let* new_functor_params =
    params |> Monad.List.map (fun (name, _) -> Name.of_string false name)
  in
  let* result_free_vars, result_typ =
    Module.to_typ
      (functor_params @ new_functor_params)
      module_name with_implicits result
  in
  let* params_free_vars, params =
    Monad.List.fold_right
      (fun (name, param) (params_free_vars, params) ->
        let* param_free_vars, param_typ = Module.to_typ [] name false param in
        let* name = Name.of_string false name in
        return (param_free_vars @ params_free_vars, (name, param_typ) :: params))
      params ([], [])
  in
  let typ =
    List.fold_right
      (fun (param_name, param_typ) typ ->
        Type.ForallModule (param_name, param_typ, typ))
      params result_typ
  in
  let typ =
    match params_free_vars with
    | [] -> typ
    | _ :: _ ->
        Type.ForallTyps
          ( params_free_vars
            |> List.map (fun { name; arity; _ } -> (name, arity)),
            typ )
  in
  return ((params_free_vars, params, result_free_vars), typ)

let to_coq_functor_parameters_modules (params_free_vars : free_vars)
    (params : (Name.t * Type.t) list) : SmartPrint.t =
  group (to_coq_grouped_free_vars params_free_vars)
  ^^ group
       (separate space
          (params
          |> List.map (fun (name, typ) ->
                 nest
                   (parens
                      (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ)))
          ))
