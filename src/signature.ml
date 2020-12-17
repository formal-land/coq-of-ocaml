(** An OCaml signature which will by transformed into a dependent record. *)
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Documentation of string
  | Module of Name.t * ModuleTyp.t
  | ModuleWithSignature of item list
  | TypExistential of Name.t
  | TypSynonym of Name.t * Type.t
  | Value of Name.t * Type.t

type t = {
  items: item list;
  typ_params: int ModuleTypParams.t }

type let_in_type = (Name.t * Name.t) list

let add_new_let_in_type
  (prefix : Name.t list) (let_in_type : let_in_type) (name : Name.t)
  : (Name.t * let_in_type) Monad.t =
  let prefixed_path_name = PathName.of_name prefix name in
  let* prefixed_name = PathName.to_name false prefixed_path_name in
  return (prefixed_name, (name, prefixed_name) :: let_in_type)

let prefix_name (is_value : bool) (prefix : Name.t list) (name : Name.t)
  : Name.t Monad.t =
  let prefixed_path_name = PathName.of_name prefix name in
  PathName.to_name is_value prefixed_path_name

let apply_let_in_type (let_in_type : let_in_type) (typ : Type.t) : Type.t =
  List.fold_left
    (fun typ (source, target) -> Type.subst_name source target typ)
    typ let_in_type

let rec items_of_types_signature
  (prefix : Name.t list)
  (let_in_type : let_in_type)
  (signature : Types.signature)
  : (item list * let_in_type) Monad.t =
  let of_types_signature_item (signature_item : Types.signature_item)
    : (item * let_in_type) Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }, _) ->
      let* name = Name.of_ident true ident in
      let* prefixed_name = prefix_name true prefix name in
      let* typ = Type.of_type_expr_without_free_vars val_type in
      let typ_args = Name.Set.elements (Type.typ_args_of_typ typ) in
      let typ_with_let_in_type =
        apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ)) in
      return (Value (prefixed_name, typ_with_let_in_type), let_in_type)
    | Sig_type (ident, { type_manifest = None; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      let* (name, let_in_type) = add_new_let_in_type prefix let_in_type name in
      return (TypExistential name, let_in_type)
    | Sig_type (ident, { type_manifest = Some typ; type_params; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      let* (name, let_in_type) = add_new_let_in_type prefix let_in_type name in
      let* typ_args = Monad.List.map Type.of_type_expr_variable type_params in
      let* typ = Type.of_type_expr_without_free_vars typ in
      let typ_with_let_in_type =
        apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ)) in
      return (TypSynonym (name, typ_with_let_in_type),let_in_type)
    | Sig_typext (_, { ext_type_path; _ }, _, _) ->
      let name = Path.name ext_type_path in
      raise
        (Error ("extensible_type_definition `" ^ name ^ "`"), let_in_type)
        ExtensibleType
        ("Extensible type '" ^ name ^ "' not handled")
    | Sig_module (ident, _, { md_type; _ }, _, _) ->
      let* name = Name.of_ident false ident in
      let* is_first_class =
        IsFirstClassModule.is_module_typ_first_class md_type None in
      begin match is_first_class with
      | Found signature_path ->
        PathName.of_path_with_convert false signature_path
          >>= fun signature_path_name ->
        let mapper ident { Types.type_manifest; type_params; _ } =
          let* name = Name.of_ident false ident in
          begin match type_manifest with
          | None -> return (Type.Arity (List.length type_params))
          | Some type_manifest ->
            (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
            Type.of_type_expr_without_free_vars type_manifest >>= fun typ ->
            let typ = Type.FunTyps (typ_args, typ) in
            return (Type.Typ typ)
          end >>= fun arity_or_typ ->
          return (Some (Tree.Item (name, arity_or_typ))) in
        ModuleTypParams.get_module_typ_typ_params
          mapper md_type >>= fun typ_params ->
        raise
          (
            Module (name, ModuleTyp.With (signature_path_name, typ_params)),
            let_in_type
          )
          Module
          (
            "Sub-module '" ^ Ident.name ident ^ "' in included " ^
            "signature.\n\n" ^
            "Sub-modules in included signatures are not handled well yet. " ^
            "It does not work if there are destructive type " ^
            "substitutions (:=) in the sub-module or type definitions in the " ^
            "sub-module's source signature. We do not develop this feature " ^
            "further as it is working in our cases.\n\n" ^
            "A safer way is to make a sub-module instead of an `include`."
          )
      | Not_found reason ->
        begin match md_type with
        | Mty_signature signature ->
          let* name = Name.of_ident false ident in
          let* (items, _) =
            items_of_types_signature (prefix @ [name]) let_in_type signature in
          return (ModuleWithSignature items, let_in_type)
        | _ ->
          raise
            (Error ("module " ^ Ident.name ident), let_in_type)
            Module
            (
              "Signature name for the module '" ^ Ident.name ident ^
              "' in included signature not found.\n\n" ^
              reason
            )
        end
      end
    | Sig_modtype (ident, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("module_type" ^ name), let_in_type)
        NotSupported
        ("Signatures '" ^ name ^ "' inside signature is not handled")
    | Sig_class (ident, _, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class" ^ name), let_in_type)
        NotSupported
        ("Class '" ^ name ^ "' not handled.")
    | Sig_class_type (ident, _, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class_type" ^ name), let_in_type)
        NotSupported
        ("Class type '" ^ name ^ "' not handled.") in
  match signature with
  | [] -> return ([], let_in_type)
  | item :: items ->
    let* (item, let_in_type) = of_types_signature_item item in
    let* (items, let_in_type) =
      items_of_types_signature prefix let_in_type items in
    return (item :: items, let_in_type)

let of_types_signature (signature : Types.signature) : t Monad.t =
  let* (items, _) = items_of_types_signature [] [] signature in
  (ModuleTypParams.get_signature_typ_params_arity signature) >>= fun typ_params ->
  return { items; typ_params }

let wrap_documentation (items_value : (item list * 'a) Monad.t)
  : (item list * 'a) Monad.t =
  let* documentation = get_documentation in
  match documentation with
  | None -> items_value
  | Some documentation ->
    let* (items, value) = items_value in
    return (Documentation documentation :: items, value)

let rec of_signature_items
  (prefix : Name.t list)
  (let_in_type : let_in_type)
  (items : signature_item list)
  (last_env : Env.t)
  : item list Monad.t =
  let of_signature_item
    (item : signature_item)
    (next_env : Env.t)
    : (item list * let_in_type) Monad.t =
    set_env item.sig_env (
    set_loc item.sig_loc (
    wrap_documentation (
    match item.sig_desc with
    | Tsig_attribute _ -> return ([], let_in_type)
    | Tsig_class _ ->
      raise
        ([Error "class"], let_in_type)
        NotSupported
        "Signature item `class` not handled."
    | Tsig_class_type _ ->
      raise
        ([Error "class_type"], let_in_type)
        NotSupported
        "Signature item `class_type` not handled."
    | Tsig_exception _ ->
      raise
        ([Error "exception"], let_in_type)
        SideEffect
        "Signature item `exception` not handled."
    | Tsig_include { incl_type; _ } ->
      set_env next_env (
      items_of_types_signature prefix let_in_type incl_type)
    | Tsig_modsubst _ ->
      raise
        ([Error "module_substitution"], let_in_type)
        NotSupported
        "We do not handle module substitutions"
    | Tsig_modtype _ ->
      raise
        ([Error "module_type"], let_in_type)
        NotSupported
        "Signatures inside signatures are not handled."
    | Tsig_module { md_id; md_type; _ } ->
      let* name = Name.of_optional_ident false md_id in
      let* prefixed_name = prefix_name false prefix name in
      begin match md_type.mty_desc with
      | Tmty_signature signature ->
        let* name = Name.of_optional_ident false md_id in
        let* items =
          of_signature_items
            (prefix @ [name]) let_in_type signature.sig_items next_env in
        return ([ModuleWithSignature items], let_in_type)
      | _ ->
        push_env (
        let* module_typ = ModuleTyp.of_ocaml md_type in
        return ([Module (prefixed_name, module_typ)], let_in_type))
      end
    | Tsig_open _ ->
      raise
        ([Error "open"], let_in_type)
        NotSupported
        "Signature item `open` not handled."
    | Tsig_recmodule _ ->
      raise
        ([Error "recursive_module"], let_in_type)
        NotSupported
        "Recursive module signatures are not handled."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = None; _ }; _ } ]) ->
      let* name = Name.of_ident false typ_id in
      let* (name, let_in_type) = add_new_let_in_type prefix let_in_type name in
      return ([TypExistential name], let_in_type)
    | Tsig_type (_, typs) | Tsig_typesubst typs ->
      begin match typs with
      | [ {
          typ_id;
          typ_type = { type_manifest = Some typ; type_params; _ };
          _
        } ] ->
        let* name = Name.of_ident false typ_id in
        let* (name, let_in_type) = add_new_let_in_type prefix let_in_type name in
        let* typ_args =
          type_params |> Monad.List.map Type.of_type_expr_variable in
        let* typ = Type.of_type_expr_without_free_vars typ in
        let typ_with_let_in_type =
          apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ)) in
        return ([TypSynonym (name, typ_with_let_in_type)], let_in_type)
      | _ ->
        raise
          ([Error "mutual_type"], let_in_type)
          NotSupported
          "Mutual type definitions in signatures not handled."
      end
    | Tsig_typext { tyext_path; _ } ->
      raise
        ([Error ("extensible_type " ^ Path.last tyext_path)], let_in_type)
        ExtensibleType
        "We do not handle extensible types"
    | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
      let* name = Name.of_ident true val_id in
      let* prefixed_name = prefix_name true prefix name in
      let* typ = Type.of_type_expr_without_free_vars ctyp_type in
      let typ_args = Name.Set.elements (Type.typ_args_of_typ typ) in
      let typ_with_let_in_type =
        apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ)) in
      return ([Value (prefixed_name, typ_with_let_in_type)], let_in_type)))) in
  match items with
  | [] -> return []
  | item :: items ->
    let next_env =
      match items with
      | { sig_env; _ } :: _ -> sig_env
      | _ -> last_env in
    let* (first_items, let_in_type) = of_signature_item item next_env in
    let* last_items = of_signature_items prefix let_in_type items last_env in
    return (first_items @ last_items)

let of_signature (signature : signature) : t Monad.t =
  push_env (
  let* items =
    of_signature_items [] [] signature.sig_items signature.sig_final_env in
  ModuleTypParams.get_signature_typ_params_arity signature.sig_type >>= fun typ_params ->
  return { items; typ_params })

let to_coq_prefixed_name (prefix : Name.t list) (name : Name.t) : SmartPrint.t =
  separate (!^ "_") (List.map Name.to_coq (prefix @ [name]))

let rec to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^ ("(* " ^ message ^ " *)")
  | Documentation message -> !^ ("(** " ^ message ^ " *)")
  | Module (name, module_typ) ->
    nest (
      Name.to_coq name ^^ !^ ":" ^^
      ModuleTyp.to_coq name module_typ ^-^ !^ ";"
    )
  | ModuleWithSignature items -> separate newline (to_coq_items items)
  | TypExistential name ->
    nest (Name.to_coq name ^^ !^ ":=" ^^ Name.to_coq name ^-^ !^ ";")
  | TypSynonym (name, typ) ->
    nest (Name.to_coq name ^^ !^ ":=" ^^ Type.to_coq None None typ ^-^ !^ ";")
  | Value (name, typ) ->
    nest (Name.to_coq name ^^ !^ ":" ^^ Type.to_coq None None typ ^-^ !^ ";")

and to_coq_items (items : item list) : SmartPrint.t list =
  List.map to_coq_item items

let rec to_coq_type_kind (arity : int) : SmartPrint.t =
  if arity = 0 then
    Pp.set
  else
    Pp.set ^^ !^ "->" ^^ to_coq_type_kind (arity - 1)

let to_coq_definition (name : Name.t) (signature : t) : SmartPrint.t =
  let typ_params : (SmartPrint.t * int) list =
    Tree.flatten signature.typ_params |> List.map (fun (path_name, arity) ->
      (ModuleTypParams.to_coq_typ_param_name path_name, arity)
    ) in
  let reversed_grouped_typ_params : (SmartPrint.t list * int) list =
    List.fold_left
      (fun grouped (typ_param, arity) ->
        match grouped with
        | [] -> [([typ_param], arity)]
        | (typ_params, arity') :: grouped' ->
          if arity = arity' then
            (typ_param :: typ_params, arity') :: grouped'
          else
            ([typ_param], arity) :: grouped
      )
      []
      typ_params in
  let grouped_typ_params =
    reversed_grouped_typ_params |>
    List.map (fun (typ_params, arity) -> (List.rev typ_params, arity)) |>
    List.rev in
  !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
  indent (
    nest (
      !^ "Record" ^^ !^ "signature" ^^
      separate space (grouped_typ_params |> List.map (fun (typ_params, arity) ->
        braces (
          separate space typ_params ^^ !^ ":" ^^ to_coq_type_kind arity
        )
      )) ^^
      nest (!^ ":" ^^ Pp.set) ^^
      !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate newline (to_coq_items signature.items)) ^^ newline ^^
      !^ "}" ^-^ !^ "."
    )
  ) ^^ newline ^^
  !^ "End" ^^ Name.to_coq name ^-^ !^ "."
