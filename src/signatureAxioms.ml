(** A signature represented by axioms for a [.mli] file. *)
open SmartPrint
open Monad.Notations

type item =
  | Error of string
  | IncludedFieldModule of Name.t * Name.t * PathName.t
  | IncludedFieldType of Name.t * Name.t * PathName.t
  | IncludedFieldValue of Name.t * Name.t list * Type.t * Name.t * PathName.t
  | Module of Name.t * t
  | ModuleAlias of Name.t * PathName.t
  | Open of Open.t
  | Signature of Name.t * Signature.t
  | TypDefinition of TypeDefinition.t
  | Value of Name.t * Name.t list * Type.t

and t = item list

let rec flatten_single_include (module_typ_desc : Typedtree.module_type_desc)
  : Typedtree.module_type_desc =
  match module_typ_desc with
  | Tmty_signature {
      sig_items = [{
        sig_desc = Tsig_include { incl_mod = { mty_desc; _ }; _ };
        _
      }];
      _
    } -> flatten_single_include mty_desc
  | _ -> module_typ_desc

let rec string_of_included_module_typ (module_typ : Typedtree.module_type)
  : string =
  match module_typ.mty_desc with
  | Tmty_ident (path, _) | Tmty_alias (path, _) -> Path.last path
  | Tmty_signature _ -> "signature"
  | Tmty_functor (ident, _, _, _) -> Ident.name ident
  | Tmty_with (module_typ, _) -> string_of_included_module_typ module_typ
  | Tmty_typeof _ -> "typeof"

let name_of_included_module_typ (module_typ : Typedtree.module_type)
  : Name.t =
  Name.of_string false ("Included_" ^ string_of_included_module_typ module_typ)

let of_types_signature (signature : Types.signature) : t Monad.t =
  signature |> Monad.List.map (function
    | Types.Sig_value (ident, { val_type; _ }) ->
      let name = Name.of_ident true ident in
      Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, _) ->
      let typ_vars = Name.Set.elements (Type.typ_args typ) in
      return (Value (name, typ_vars, typ))
    | Sig_type (ident, { type_params; _ }, _) ->
      (* We ignore the type manifest so that we do not unroll unwanted type
         definitions. *)
      let name = Name.of_ident false ident in
      Monad.List.map Type.of_type_expr_variable type_params >>= fun typ_params ->
      return (TypDefinition (TypeDefinition.Abstract (name, typ_params)))
    | Sig_typext _ ->
      raise (Error "type_extension") NotSupported "Type extension not handled"
    | Sig_module _ ->
      raise (Error "module") NotSupported "Module not handled in included signature"
    | Sig_modtype _ ->
      raise (Error "module_type") NotSupported "Module type not handled in included signature"
    | Sig_class _ ->
      raise (Error "class") NotSupported "Class not handled"
    | Sig_class_type _ ->
      raise (Error "class_type") NotSupported "Class type not handled"
  )

let of_first_class_types_signature
  (module_name : Name.t)
  (signature_path : Path.t)
  (signature : Types.signature)
  (final_env : Env.t)
  : t Monad.t =
  let field_path_name name =
    PathName.of_path_and_name_with_convert signature_path name in
  set_env final_env (
  signature |> Monad.List.filter_map (function
    | Types.Sig_value (ident, { val_type; _ }) ->
      let name = Name.of_ident true ident in
      Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, new_typ_vars) ->
      return (Some (
        IncludedFieldValue (
          name,
          Name.Set.elements new_typ_vars,
          typ,
          module_name,
          field_path_name name
        )
      ))
    | Sig_type (ident, _, _) ->
      let name = Name.of_ident false ident in
      return (Some (
        IncludedFieldType (name, module_name, field_path_name name)
      ))
    | Sig_typext _ ->
      raise None NotSupported "Type extension not handled"
    | Sig_module (ident, _, _) ->
      let name = Name.of_ident false ident in
      return (Some (
        IncludedFieldModule (name, module_name, field_path_name name)
      ))
    | Sig_modtype _ ->
      raise None NotSupported "Module type not handled in included signature"
    | Sig_class _ ->
      raise None NotSupported "Class not handled"
    | Sig_class_type _ ->
      raise None NotSupported "Class type not handled"
  ))

let rec of_signature (signature : Typedtree.signature) : t Monad.t =
  let of_signature_item
    (signature_item : Typedtree.signature_item) (final_env : Env.t)
    : item list Monad.t =
    set_env signature_item.sig_env (
    set_loc (Loc.of_location signature_item.sig_loc) (
    match signature_item.sig_desc with
    | Tsig_attribute _ ->
      raise
        [Error "attribute"]
        NotSupported
        "Signature item `attribute` not handled"
    | Tsig_class _ ->
      raise
        [Error "class"]
        NotSupported
        "Signature item `class` not handled"
    | Tsig_class_type _ ->
      raise
        [Error "class_type"]
        NotSupported
        "Signature item `class_type` not handled"
    | Tsig_exception { ext_id; _ } ->
      raise
        [Error ("exception " ^ Ident.name ext_id)]
        SideEffect
        "Signature item `exception` not handled"
    | Tsig_include { incl_mod; incl_type; _} ->
      let module_name = name_of_included_module_typ incl_mod in
      let signature_path = ModuleTyp.get_module_typ_path_name incl_mod in
      begin match signature_path with
      | None -> of_types_signature incl_type
      | Some signature_path ->
        ModuleTyp.of_ocaml incl_mod >>= fun module_typ ->
        let typ = ModuleTyp.to_typ module_typ in
        of_first_class_types_signature
          module_name signature_path incl_type final_env >>= fun fields ->
        return (Value (module_name, [], typ) :: fields)
      end
    | Tsig_modtype { mtd_type = None; _ } ->
      raise
        [Error "abstract_module_type"]
        NotSupported
        "Abstract module type not handled"
    | Tsig_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ } ->
      let name = Name.of_ident false mtd_id in
      begin match mty_desc with
      | Tmty_signature signature ->
        Signature.of_signature signature >>= fun signature ->
        return [Signature (name, signature)]
      | _ ->
        raise
          [Error "unhandled_module_type"]
          NotSupported
          "Unhandled kind of module type"
      end
    | Tsig_module { md_id; md_type = { mty_desc; _ }; _ } ->
      let name = Name.of_ident false md_id in
      let mty_desc = flatten_single_include mty_desc in
      begin match mty_desc with
      | Tmty_alias (path, _) ->
        let path_name = PathName.of_path_with_convert false path in
        return [ModuleAlias (name, path_name)]
      | Tmty_signature signature ->
        of_signature signature >>= fun signature ->
        return [Module (name, signature)]
      | Tmty_typeof { mod_type; _} ->
        get_env >>= fun env ->
        begin match Mtype.scrape_for_type_of ~remove_aliases:true env mod_type with
        | Types.Mty_signature signature ->
          of_types_signature signature >>= fun signature ->
          return [Module (name, signature)]
        | _ ->
          raise
            [Error "unhandled_kind_of_typeof"]
            NotSupported
            "We do not support this kind of typeof"
        end
      | _ ->
        ModuleTyp.of_ocaml_desc mty_desc >>= fun module_typ ->
        let typ = ModuleTyp.to_typ module_typ in
        return [Value (name, [], typ)]
      end
    | Tsig_open open_description ->
      let o = Open.of_ocaml open_description in
      return [Open o]
    | Tsig_recmodule _ ->
      raise
        [Error "recursive_module"]
        NotSupported
        "Recursive module signatures are not handled"
    | Tsig_type (_, typs) ->
      TypeDefinition.of_ocaml typs >>= fun typ_definition ->
      return [TypDefinition typ_definition]
    | Tsig_typext { tyext_path; _ } ->
      raise
        [Error ("extensible_type " ^ Path.last tyext_path)]
        NotSupported
        "Extensible types are not handled."
    | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
      let name = Name.of_ident true val_id in
      Type.of_typ_expr true Name.Map.empty ctyp_type >>= fun (typ, _, _) ->
      let typ_vars = Name.Set.elements (Type.typ_args typ) in
      return [Value (name, typ_vars, typ)])) in
  Monad.List.fold_right
    (fun signature_item (signature, final_env) ->
      let env = signature_item.Typedtree.sig_env in
      of_signature_item signature_item final_env >>= fun signature_item ->
      return (signature_item @ signature, env)
    )
    signature.sig_items
    ([], signature.sig_final_env) >>= fun (signature, _) ->
  return signature

let to_coq_included_field (module_name : Name.t) (field_name : PathName.t)
  : SmartPrint.t =
  MixedPath.to_coq (
    MixedPath.Access (PathName.of_name [] module_name, [field_name], false)
  )

let rec to_coq (signature : t) : SmartPrint.t =
  let to_coq_item (signature_item : item) : SmartPrint.t =
    match signature_item with
    | Error message -> !^ ("(* " ^ message ^ " *)")
    | IncludedFieldModule (name, module_name, field_name) ->
      let field = to_coq_included_field module_name field_name in
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^
        nest (!^ "existT" ^^ !^ "(fun _ => _)" ^^ !^ "tt" ^^ field) ^-^ !^ "."
      )
    | IncludedFieldType (name, module_name, field_name) ->
      let field = to_coq_included_field module_name field_name in
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^
        field ^-^ !^ "."
      )
    | IncludedFieldValue (name, typ_params, typ, module_name, field_name) ->
      let field = to_coq_included_field module_name field_name in
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^
        begin match typ_params with
        | [] -> empty
        | _ :: _ ->
          nest (braces (
            separate space (List.map Name.to_coq typ_params) ^^ !^ ":" ^^ !^ "Set"
          ))
        end ^^
        !^ ":" ^^ Type.to_coq None None typ ^^
        !^ ":=" ^^
        field ^-^ !^ "."
      )
    | Module (name, signature) ->
      !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
      indent (to_coq signature) ^^ newline ^^
      !^ "End" ^^ Name.to_coq name ^-^ !^ "."
    | ModuleAlias (name, path_name) ->
      !^ "Module" ^^ Name.to_coq name ^^ !^ ":=" ^^
      PathName.to_coq path_name ^-^ !^ "."
    | Open o -> Open.to_coq o
    | Signature (name, signature) -> Signature.to_coq_definition name signature
    | TypDefinition typ_definition -> TypeDefinition.to_coq typ_definition
    | Value (name, typ_vars, typ) ->
      nest (
        !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
        (match typ_vars with
        | [] -> empty
        | _ :: _ ->
          !^ "forall" ^^ braces (group (
            separate space (List.map Name.to_coq typ_vars) ^^
            !^ ":" ^^ Pp.set)) ^-^ !^ ",") ^^
        Type.to_coq None None typ ^-^ !^ "."
      ) in
  separate (newline ^^ newline) (signature |> List.map to_coq_item)
