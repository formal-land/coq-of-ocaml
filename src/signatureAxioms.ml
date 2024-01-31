open SmartPrint
(** A signature represented by axioms for a [.mli] file. *)

open Monad.Notations

type item =
  | Error of string
  | IncludedFieldModule of Name.t * Name.t * PathName.t
  | IncludedFieldType of Name.t * Name.t * PathName.t
  | IncludedFieldValue of Name.t * Name.t list * Type.t * Name.t * PathName.t
  | Module of Name.t * t
  | ModuleAlias of Name.t * PathName.t
  | ModuleFreeVar of
      ModuleTyp.free_vars * (Name.t * Type.t) list * ModuleTyp.free_var
  | Signature of Name.t * Signature.t
  | TypDefinition of TypeDefinition.t
  | Value of Name.t * Name.t list * Type.t

and t = item list

let rec string_of_included_module_typ_aux (module_typ : Typedtree.module_type) :
    string =
  match module_typ.mty_desc with
  | Tmty_ident (path, _) | Tmty_alias (path, _) -> Path.last path
  | Tmty_signature _ -> "signature"
  | Tmty_functor _ -> "functor"
  | Tmty_with (module_typ, _) -> string_of_included_module_typ_aux module_typ
  | Tmty_typeof _ -> "typeof"

let string_of_included_module_typ (module_typ : Typedtree.module_type) : string
    =
  "Included_" ^ string_of_included_module_typ_aux module_typ

let of_types_signature (signature : Types.signature) : t Monad.t =
  signature
  |> Monad.List.map (function
       | Types.Sig_value (ident, { val_type; _ }, _) ->
           let* name = Name.of_ident true ident in
           Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, _) ->
           let typ_vars = Name.Set.elements (Type.typ_args_of_typ typ) in
           return (Value (name, typ_vars, typ))
       | Sig_type (ident, { type_params; _ }, _, _) ->
           (* We ignore the type manifest so that we do not unroll unwanted type
              definitions. *)
           let* name = Name.of_ident false ident in
           Monad.List.map Type.of_type_expr_variable type_params
           >>= fun typ_params ->
           return (TypDefinition (TypeDefinition.Abstract (name, typ_params)))
       | Sig_typext _ ->
           raise (Error "type_extension") ExtensibleType
             "We do not handle extensible types here"
       | Sig_module _ ->
           raise (Error "module") NotSupported
             "Module not handled in included signature"
       | Sig_modtype _ ->
           raise (Error "module_type") NotSupported
             "Module type not handled in included signature"
       | Sig_class _ -> raise (Error "class") NotSupported "Class not handled"
       | Sig_class_type _ ->
           raise (Error "class_type") NotSupported "Class type not handled")

let of_first_class_types_signature (module_name : Name.t)
    (signature_path : Path.t) (signature : Types.signature) (final_env : Env.t)
    : t Monad.t =
  let get_field_path_name name =
    PathName.of_path_and_name_with_convert signature_path name
  in
  set_env final_env
    (signature
    |> Monad.List.filter_map (function
         | Types.Sig_value (ident, { val_type; _ }, _) ->
             let* name = Name.of_ident true ident in
             get_field_path_name name >>= fun field_path_name ->
             Type.of_typ_expr true Name.Map.empty val_type
             >>= fun (typ, _, new_typ_vars) ->
             return
               (Some
                  (IncludedFieldValue
                     ( name,
                       List.map fst new_typ_vars,
                       typ,
                       module_name,
                       field_path_name )))
         | Sig_type (ident, _, _, _) ->
             let* name = Name.of_ident false ident in
             get_field_path_name name >>= fun field_path_name ->
             return
               (Some (IncludedFieldType (name, module_name, field_path_name)))
         | Sig_typext _ -> return None
         | Sig_module (ident, _, _, _, _) ->
             let* name = Name.of_ident false ident in
             get_field_path_name name >>= fun field_path_name ->
             return
               (Some (IncludedFieldModule (name, module_name, field_path_name)))
         | Sig_modtype _ ->
             raise None NotSupported
               "Module type not handled in included signature"
         | Sig_class _ -> raise None NotSupported "Class not handled"
         | Sig_class_type _ -> raise None NotSupported "Class type not handled")
    )

let rec of_signature (signature : Typedtree.signature) : t Monad.t =
  let of_signature_item (signature_item : Typedtree.signature_item)
      (final_env : Env.t) : item list Monad.t =
    set_env signature_item.sig_env
      (set_loc signature_item.sig_loc
         (match signature_item.sig_desc with
         | Tsig_attribute _ ->
             raise [ Error "attribute" ] NotSupported
               "Signature item `attribute` not handled"
         | Tsig_class _ ->
             raise [ Error "class" ] NotSupported
               "Signature item `class` not handled"
         | Tsig_class_type class_typ_declarations -> (
             match class_typ_declarations with
             | [ { ci_params; ci_id_class_type; ci_expr; _ } ] -> (
                 ci_params
                 |> List.map (fun ({ Typedtree.ctyp_type; _ }, _) -> ctyp_type)
                 |> AdtParameters.of_ocaml
                 >>= fun typ_params ->
                 let typ_params = AdtParameters.get_parameters typ_params in
                 let typ_params =
                   typ_params |> List.map (fun field -> (field, Kind.Set))
                 in
                 let* name = Name.of_ident false ci_id_class_type in
                 match ci_expr with
                 | {
                  cltyp_desc = Tcty_signature class_signature;
                  cltyp_env;
                  cltyp_loc;
                  _;
                 } ->
                     set_env cltyp_env
                       (set_loc cltyp_loc
                          ( class_signature.csig_fields
                          |> Monad.List.filter_map (fun class_typ_field ->
                                 set_loc class_typ_field.Typedtree.ctf_loc
                                   (match class_typ_field.ctf_desc with
                                   | Tctf_method
                                       (field_name, _, _, { ctyp_type; _ }) ->
                                       let* field_name =
                                         Name.of_string false field_name
                                       in
                                       Type.of_typ_expr false Name.Map.empty
                                         ctyp_type
                                       >>= fun (field_typ, _, _) ->
                                       return (Some (field_name, field_typ))
                                   | _ ->
                                       raise None NotSupported
                                         "We do not handle this form of field \
                                          of class type"))
                          >>= fun fields ->
                            return
                              [
                                TypDefinition
                                  (TypeDefinition.Record
                                     (name, typ_params, fields, false));
                              ] ))
                 | _ ->
                     raise
                       [ Error "unhandled_class_type" ]
                       NotSupported "We do not handle this form of class type")
             | _ ->
                 raise
                   [ Error "mutual_class_types" ]
                   NotSupported
                   "We do not handle mutually recursive declaration of class \
                    types")
         | Tsig_exception { tyexn_constructor; _ } ->
             let* typ_defs =
               Structure.typ_definitions_of_typ_extension_raw tyexn_constructor
             in
             return (typ_defs |> List.map (fun typ_def -> TypDefinition typ_def))
         | Tsig_include { incl_mod; incl_type; _ } -> (
             let module_name = string_of_included_module_typ incl_mod in
             let signature_path = ModuleTyp.get_module_typ_path_name incl_mod in
             match signature_path with
             | None -> of_types_signature incl_type
             | Some signature_path ->
                 ModuleTyp.of_ocaml incl_mod >>= fun module_typ ->
                 let* (free_vars_params, params, free_vars), typ =
                   ModuleTyp.to_typ [] module_name false module_typ
                 in
                 let free_vars =
                   free_vars
                   |> List.map (fun free_var ->
                          ModuleFreeVar (free_vars_params, params, free_var))
                 in
                 let* module_name = Name.of_string false module_name in
                 of_first_class_types_signature module_name signature_path
                   incl_type final_env
                 >>= fun fields ->
                 return (free_vars @ (Value (module_name, [], typ) :: fields)))
         | Tsig_modsubst _ ->
             raise
               [ Error "unhandled_module_substitution" ]
               NotSupported "We do not handle module substitution"
         | Tsig_modtype { mtd_type = None; _ }
         | Tsig_modtypesubst { mtd_type = None; _ } ->
             raise
               [ Error "abstract_module_type" ]
               NotSupported "Abstract module type not handled"
         | Tsig_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ }
         | Tsig_modtypesubst { mtd_id; mtd_type = Some { mty_desc; _ }; _ } -> (
             let* name = Name.of_ident false mtd_id in
             match mty_desc with
             | Tmty_signature signature ->
                 Signature.of_signature signature >>= fun signature ->
                 return [ Signature (name, signature) ]
             | _ ->
                 raise
                   [ Error "unhandled_module_type" ]
                   NotSupported "Unhandled kind of module type")
         | Tsig_module { md_id; md_type = { mty_desc; _ }; _ } -> (
             let* name = Name.of_optional_ident false md_id in
             match mty_desc with
             | Tmty_alias (path, _) ->
                 PathName.of_path_with_convert false path >>= fun path_name ->
                 return [ ModuleAlias (name, path_name) ]
             | Tmty_signature signature ->
                 of_signature signature >>= fun signature ->
                 return [ Module (name, signature) ]
             | Tmty_typeof { mod_type; _ } -> (
                 get_env >>= fun env ->
                 match
                   Mtype.scrape_for_type_of ~remove_aliases:true env mod_type
                 with
                 | Types.Mty_signature signature ->
                     of_types_signature signature >>= fun signature ->
                     return [ Module (name, signature) ]
                 | _ ->
                     raise
                       [ Error "unhandled_kind_of_typeof" ]
                       NotSupported "We do not support this kind of typeof")
             | _ ->
                 ModuleTyp.of_ocaml_desc mty_desc >>= fun module_typ ->
                 let id = Name.string_of_optional_ident md_id in
                 let* (free_vars_params, params, free_vars), typ =
                   ModuleTyp.to_typ [] id false module_typ
                 in
                 let free_vars =
                   free_vars
                   |> List.map (fun free_var ->
                          ModuleFreeVar (free_vars_params, params, free_var))
                 in
                 return (free_vars @ [ Value (name, [], typ) ]))
         | Tsig_open _ -> return []
         | Tsig_recmodule _ ->
             raise
               [ Error "recursive_module" ]
               NotSupported "Recursive module signatures are not handled"
         | Tsig_type (_, typs) | Tsig_typesubst typs ->
             (* Because types may be recursive, so we need the types to already be in
                the environment. This is useful for example for the detection of
                phantom types. *)
             set_env final_env
               ( TypeDefinition.of_ocaml typs >>= fun typ_definition ->
                 return [ TypDefinition typ_definition ] )
         | Tsig_typext { tyext_constructors; _ } ->
             let* typ_defs =
               tyext_constructors
               |> Monad.List.concat_map
                    Structure.typ_definitions_of_typ_extension_raw
             in
             return (typ_defs |> List.map (fun typ_def -> TypDefinition typ_def))
         | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
             let* name = Name.of_ident true val_id in
             Type.of_typ_expr true Name.Map.empty ctyp_type
             >>= fun (typ, _, _) ->
             let typ_vars = Name.Set.elements (Type.typ_args_of_typ typ) in
             return [ Value (name, typ_vars, typ) ]))
  in
  Monad.List.fold_right
    (fun signature_item (signature, final_env) ->
      let env = signature_item.Typedtree.sig_env in
      of_signature_item signature_item final_env >>= fun signature_item ->
      return (signature_item @ signature, env))
    signature.sig_items
    ([], signature.sig_final_env)
  >>= fun (signature, _) -> return signature

let to_coq_included_field (module_name : Name.t) (field_name : PathName.t) :
    SmartPrint.t =
  MixedPath.to_coq
    (MixedPath.Access (PathName.of_name [] module_name, [ field_name ]))

let rec to_coq (signature : t) : SmartPrint.t =
  let to_coq_item (signature_item : item) : SmartPrint.t =
    match signature_item with
    | Error message -> !^("(* " ^ message ^ " *)")
    | IncludedFieldModule (name, module_name, field_name) ->
        let field = to_coq_included_field module_name field_name in
        nest (!^"Definition" ^^ Name.to_coq name ^^ !^":=" ^^ field ^-^ !^".")
    | IncludedFieldType (name, module_name, field_name) ->
        let field = to_coq_included_field module_name field_name in
        nest (!^"Definition" ^^ Name.to_coq name ^^ !^":=" ^^ field ^-^ !^".")
    | IncludedFieldValue (name, typ_params, typ, module_name, field_name) ->
        let field = to_coq_included_field module_name field_name in
        nest
          (!^"Definition" ^^ Name.to_coq name
          ^^ (match typ_params with
             | [] -> empty
             | _ :: _ ->
                 nest
                   (braces
                      (separate space (List.map Name.to_coq typ_params)
                      ^^ !^":" ^^ !^"Set")))
          ^^ !^":" ^^ Type.to_coq None None typ ^^ !^":=" ^^ field ^-^ !^".")
    | Module (name, signature) ->
        !^"Module" ^^ Name.to_coq name ^-^ !^"." ^^ newline
        ^^ indent (to_coq signature)
        ^^ newline ^^ !^"End" ^^ Name.to_coq name ^-^ !^"."
    | ModuleAlias (name, path_name) ->
        !^"Module" ^^ Name.to_coq name ^^ !^":=" ^^ PathName.to_coq path_name
        ^-^ !^"."
    | ModuleFreeVar (free_vars_params, params, free_var) ->
        let { ModuleTyp.name; arity; _ } = free_var in
        nest
          (!^"Parameter" ^^ Name.to_coq name ^^ !^":"
          ^^ nest
               ((match params with
                | [] -> empty
                | _ :: _ ->
                    !^"forall"
                    ^^ ModuleTyp.to_coq_functor_parameters_modules
                         free_vars_params params
                    ^-^ !^",")
               ^^ Pp.typ_arity arity ^-^ !^"."))
    | Signature (name, signature) ->
        Signature.to_coq_definition None name signature
    | TypDefinition typ_definition -> TypeDefinition.to_coq None typ_definition
    | Value (name, typ_vars, typ) ->
        nest
          (!^"Parameter" ^^ Name.to_coq name ^^ !^":"
          ^^ Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
                 !^"forall"
                 ^^ braces (group (typ_vars ^^ !^":" ^^ Pp.set))
                 ^-^ !^",")
          ^^ Type.to_coq None None typ ^-^ !^".")
  in
  separate (newline ^^ newline) (signature |> List.map to_coq_item)
