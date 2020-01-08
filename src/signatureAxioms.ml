(** A signature represented by axioms for a [.mli] file. *)
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Module of Name.t * t
  | Signature of Name.t * Signature.t
  | TypDefinition of TypeDefinition.t
  | Value of Name.t * Name.t list * Type.t

and t = item list

let rec of_types_signature (signature : Types.signature) : t Monad.t =
  let of_types_signature_item
    (signature_item : Types.signature_item)
    : item Monad.t =
    match signature_item with
    | Sig_class _ ->
      raise (Error "class") NotSupported "Signature item `class` not handled"
    | Sig_class_type _ ->
      raise (Error "class_type") NotSupported "Signature item `class_type` not handled"
    | Sig_modtype (_, { mtd_type = None; _ }) ->
      raise (Error "abstract_module_type") NotSupported "Abstract module type not handled"
    | Sig_modtype (ident, { mtd_type = Some module_typ; _ }) ->
      let name = Name.of_ident false ident in
      begin match module_typ with
      | Mty_signature signature ->
        Signature.of_types_signature signature >>= fun signature ->
        return (Signature (name, signature))
      | _ ->
        raise
          (Error "unhandled_module_type")
          NotSupported
          "Unhandled kind of module type"
      end
    | Sig_module (ident, { md_type; _ }, _) ->
      let name = Name.of_ident false ident in
      of_types_module_type md_type >>= fun signature ->
      return (Module (name, signature))
    | Sig_type (ident, { type_manifest; type_params; _}, _) ->
      let name = Name.of_ident false ident in
      (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      begin match type_manifest with
      | None ->
        return (TypDefinition (TypeDefinition.Abstract (name, typ_args)))
      | Some typ ->
        Type.of_typ_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
        return (TypDefinition (TypeDefinition.Synonym (name, typ_args, typ)))
      end
    | Sig_typext _ ->
      raise (Error "extensible_type") NotSupported "Extensible types are not handled"
    | Sig_value (ident, { val_type; _ }) ->
      let name = Name.of_ident true ident in
      Type.of_type_expr_without_free_vars val_type >>= fun typ ->
      let typ_vars = Name.Set.elements (Type.typ_args typ) in
      return (Value (name, typ_vars, typ)) in
  Monad.List.map of_types_signature_item signature

and of_types_module_type (module_typ : Types.module_type) : t Monad.t =
  get_env >>= fun env ->
  let module_typ = Mtype.scrape env module_typ in
  match module_typ with
  | Mty_alias _ | Mty_ident _ ->
    let error_message = "Unhandled inlined abstract module" in
    raise [Error ("(* " ^ error_message ^ " *)")] NotSupported error_message
  | Mty_signature signature -> of_types_signature signature
  | Mty_functor _ ->
    let error_message = "Unhandled functor" in
    raise [Error ("(* " ^ error_message ^ " *)")] NotSupported error_message

let rec of_signature (signature : signature) : t Monad.t =
  let of_signature_item (signature_item : signature_item) : item option Monad.t =
    set_env signature_item.sig_env (
    set_loc (Loc.of_location signature_item.sig_loc) (
    match signature_item.sig_desc with
    | Tsig_attribute _ ->
      raise (Some (Error "attribute")) NotSupported "Signature item `attribute` not handled"
    | Tsig_class _ ->
      raise (Some (Error "class")) NotSupported "Signature item `class` not handled"
    | Tsig_class_type _ ->
      raise (Some (Error "class_type")) NotSupported "Signature item `class_type` not handled"
    | Tsig_exception { ext_id; _ } ->
      raise (Some (Error ("(* exception " ^ Ident.name ext_id ^ " *)"))) SideEffect "Signature item `exception` not handled"
    | Tsig_include _ ->
      raise (Some (Error "include")) NotSupported "Signature item `include` not handled"
    | Tsig_modtype { mtd_type = None; _ } ->
      raise (Some (Error "abstract_module_type")) NotSupported "Abstract module type not handled"
    | Tsig_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ } ->
      let name = Name.of_ident false mtd_id in
      begin match mty_desc with
      | Tmty_signature signature ->
        Signature.of_signature signature >>= fun signature ->
        return (Some (Signature (name, signature)))
      | _ ->
        raise
          (Some (Error "unhandled_module_type"))
          NotSupported
          "Unhandled kind of module type"
      end
    | Tsig_module { md_id; md_type = { mty_desc; mty_type; _ }; _ } ->
      let name = Name.of_ident false md_id in
      begin match mty_desc with
      | Tmty_signature signature ->
        of_signature signature >>= fun signature ->
        return (Some (Module (name, signature)))
      | _ ->
        of_types_module_type mty_type >>= fun signature ->
        return (Some (Module (name, signature)))
      end
    | Tsig_open _ -> return None
    | Tsig_recmodule _ ->
      raise (Some (Error "recursive_module")) NotSupported "Recursive module signatures are not handled"
    | Tsig_type (_, typs) ->
      TypeDefinition.of_ocaml typs >>= fun typ_definition ->
      return (Some (TypDefinition typ_definition))
    | Tsig_typext _ ->
      raise (Some (Error "extensible_type")) NotSupported "Extensible types are not handled"
    | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
      let name = Name.of_ident true val_id in
      Type.of_type_expr_without_free_vars ctyp_type >>= fun typ ->
      let typ_vars = Name.Set.elements (Type.typ_args typ) in
      return (Some (Value (name, typ_vars, typ))))) in
  (signature.sig_items |> Monad.List.filter_map of_signature_item) >>= fun items ->
  return items

let rec to_coq (signature : t) : SmartPrint.t =
  let to_coq_item (signature_item : item) : SmartPrint.t =
    match signature_item with
    | Error message -> !^ message
    | Module (name, signature) ->
      !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
      indent (to_coq signature) ^^ newline ^^
      !^ "End" ^^ Name.to_coq name ^-^ !^ "."
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
