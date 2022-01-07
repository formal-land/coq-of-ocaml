open SmartPrint
(** An OCaml signature which will by transformed into a dependent record. *)

open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Documentation of string
  | Module of Name.t * Type.t
  | ModuleWithSignature of item list
  | TypExistential of Name.t
  | TypSynonym of Name.t * Type.t
  | Value of Name.t * Type.t

type t = { items : item list; typ_params : (Name.t * int) list }
type let_in_type = (Name.t * Name.t) list

let add_new_let_in_type (prefix : string list) (let_in_type : let_in_type)
    (id : Ident.t) : (Name.t * let_in_type) Monad.t =
  let* name = Name.of_ident false id in
  let* prefixed_name = Name.of_strings false (prefix @ [ Ident.name id ]) in
  return (prefixed_name, (name, prefixed_name) :: let_in_type)

let apply_let_in_type (let_in_type : let_in_type) (typ : Type.t) : Type.t =
  List.fold_left
    (fun typ (source, target) -> Type.subst_name source target typ)
    typ let_in_type

let rec items_of_types_signature (prefix : string list)
    (let_in_type : let_in_type) (signature : Types.signature) :
    (item list * let_in_type) Monad.t =
  let of_types_signature_item (signature_item : Types.signature_item) :
      (item * let_in_type) Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }, _) ->
        let* prefixed_name =
          Name.of_strings true (prefix @ [ Ident.name ident ])
        in
        let* typ = Type.of_type_expr_without_free_vars val_type in
        let typ_args =
          Type.typ_args_of_typ typ |> Name.Set.elements
          |> List.map (fun typ -> (typ, 0))
        in
        let typ_with_let_in_type =
          apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ))
        in
        return (Value (prefixed_name, typ_with_let_in_type), let_in_type)
    | Sig_type (ident, { type_manifest = None; _ }, _, _) ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        return (TypExistential name, let_in_type)
    | Sig_type (ident, { type_manifest = Some typ; type_params; _ }, _, _) ->
        let* name, let_in_type = add_new_let_in_type prefix let_in_type ident in
        let* typ_args =
          type_params
          |> Monad.List.map (fun typ_param ->
                 let* typ = Type.of_type_expr_variable typ_param in
                 return (typ, 0))
        in
        let* typ = Type.of_type_expr_without_free_vars typ in
        let typ_with_let_in_type =
          apply_let_in_type let_in_type (Type.ForallTyps (typ_args, typ))
        in
        return (TypSynonym (name, typ_with_let_in_type), let_in_type)
    | Sig_typext (_, { ext_type_path; _ }, _, _) ->
        let name = Path.name ext_type_path in
        raise
          (Error ("extensible_type_definition `" ^ name ^ "`"), let_in_type)
          ExtensibleType
          ("Extensible type '" ^ name ^ "' not handled")
    | Sig_module (ident, _, { md_type; _ }, _, _) -> (
        let* name = Name.of_ident false ident in
        let* is_first_class =
          IsFirstClassModule.is_module_typ_first_class md_type None
        in
        match is_first_class with
        | Found signature_path ->
            PathName.of_path_with_convert false signature_path
            >>= fun signature_path_name ->
            let mapper ident { Types.type_manifest; type_params; _ } =
              let name = Ident.name ident in
              (match type_manifest with
              | None -> return (Type.Arity (List.length type_params))
              | Some type_manifest ->
                  type_params |> Monad.List.map Type.of_type_expr_variable
                  >>= fun typ_args ->
                  Type.of_type_expr_without_free_vars type_manifest
                  >>= fun typ ->
                  let typ = Type.FunTyps (typ_args, typ) in
                  return (Type.Typ typ))
              >>= fun arity_or_typ ->
              return (Some (Tree.Item (name, arity_or_typ)))
            in
            let* typ_params =
              ModuleTypParams.get_module_typ_typ_params mapper md_type
            in
            let* typ_params =
              Tree.flatten typ_params
              |> Monad.List.map (fun (path, arity_or_typ) ->
                     let* name = Name.of_strings false path in
                     let* typ_name =
                       Name.of_strings false (Ident.name ident :: path)
                     in
                     match arity_or_typ with
                     | Type.Arity _ ->
                         return (name, Some (Type.Variable typ_name))
                     | Typ typ -> return (name, Some typ))
            in
            raise
              ( Module (name, Type.Signature (signature_path_name, typ_params)),
                let_in_type )
              Module
              ("Sub-module '" ^ Ident.name ident ^ "' in included "
             ^ "signature.\n\n"
             ^ "Sub-modules in included signatures are not handled well yet. "
             ^ "It does not work if there are destructive type "
             ^ "substitutions (:=) in the sub-module or type definitions in \
                the "
             ^ "sub-module's source signature. We do not develop this feature "
             ^ "further as it is working in our cases.\n\n"
             ^ "A safer way is to make a sub-module instead of an `include`.")
        | Not_found reason -> (
            match md_type with
            | Mty_signature signature ->
                let prefix = prefix @ [ Ident.name ident ] in
                let* items, _ =
                  items_of_types_signature prefix let_in_type signature
                in
                return (ModuleWithSignature items, let_in_type)
            | _ ->
                raise
                  (Error ("module " ^ Ident.name ident), let_in_type)
                  Module
                  ("Signature name for the module '" ^ Ident.name ident
                 ^ "' in included signature not found.\n\n" ^ reason)))
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
          ("Class type '" ^ name ^ "' not handled.")
  in
  match signature with
  | [] -> return ([], let_in_type)
  | item :: items ->
      let* item, let_in_type = of_types_signature_item item in
      let* items, let_in_type =
        items_of_types_signature prefix let_in_type items
      in
      return (item :: items, let_in_type)

let of_types_signature (signature : Types.signature) : t Monad.t =
  let* items, _ = items_of_types_signature [] [] signature in
  let* typ_params = ModuleTypParams.get_signature_typ_params_arity signature in
  let* typ_params =
    Tree.flatten typ_params
    |> Monad.List.map (fun (path, arity) ->
           let* name = Name.of_strings false path in
           return (name, arity))
  in
  return { items; typ_params }

let wrap_documentation (items_value : (item list * 'a) Monad.t) :
    (item list * 'a) Monad.t =
  let* documentation = get_documentation in
  match documentation with
  | None -> items_value
  | Some documentation ->
      let* items, value = items_value in
      return (Documentation documentation :: items, value)

let rec of_signature_items (prefix : string list) (let_in_type : let_in_type)
    (items : signature_item list) (last_env : Env.t) : item list Monad.t =
  let of_signature_item (item : signature_item) (next_env : Env.t) :
      (item list * let_in_type) Monad.t =
    set_env item.sig_env
      (set_loc item.sig_loc
         (wrap_documentation
            (match item.sig_desc with
            | Tsig_attribute _ -> return ([], let_in_type)
            | Tsig_class _ ->
                raise
                  ([ Error "class" ], let_in_type)
                  NotSupported "Signature item `class` not handled."
            | Tsig_class_type _ ->
                raise
                  ([ Error "class_type" ], let_in_type)
                  NotSupported "Signature item `class_type` not handled."
            | Tsig_exception _ -> return ([], let_in_type)
            | Tsig_include { incl_type; _ } ->
                set_env next_env
                  (items_of_types_signature prefix let_in_type incl_type)
            | Tsig_modsubst _ ->
                raise
                  ([ Error "module_substitution" ], let_in_type)
                  NotSupported "We do not handle module substitutions"
            | Tsig_modtype _ ->
                raise
                  ([ Error "module_type" ], let_in_type)
                  NotSupported "Signatures inside signatures are not handled."
            | Tsig_module { md_id = Some ident; _ }
              when Ident.name ident = "Internal_for_tests" ->
                return ([], let_in_type)
            | Tsig_module { md_id; md_type; _ } -> (
                let id =
                  match md_id with
                  | Some md_id -> Ident.name md_id
                  | None -> "_"
                in
                match md_type.mty_desc with
                | Tmty_signature signature ->
                    let prefix = prefix @ [ id ] in
                    let* items =
                      of_signature_items prefix let_in_type signature.sig_items
                        next_env
                    in
                    return ([ ModuleWithSignature items ], let_in_type)
                | _ ->
                    push_env
                      (let prefixed_id = String.concat "_" (prefix @ [ id ]) in
                       let* prefixed_name = Name.of_string false prefixed_id in
                       let* module_typ = ModuleTyp.of_ocaml md_type in
                       let* _, typ =
                         ModuleTyp.to_typ [] prefixed_id false module_typ
                       in
                       return ([ Module (prefixed_name, typ) ], let_in_type)))
            | Tsig_open _ -> return ([], let_in_type)
            | Tsig_recmodule _ ->
                raise
                  ([ Error "recursive_module" ], let_in_type)
                  NotSupported "Recursive module signatures are not handled."
            | Tsig_type
                (_, [ { typ_id; typ_type = { type_manifest = None; _ }; _ } ])
              ->
                let* name, let_in_type =
                  add_new_let_in_type prefix let_in_type typ_id
                in
                return ([ TypExistential name ], let_in_type)
            | Tsig_type (_, typs) | Tsig_typesubst typs -> (
                match typs with
                | [
                 {
                   typ_id;
                   typ_type = { type_manifest = Some typ; type_params; _ };
                   _;
                 };
                ] ->
                    let* name, let_in_type =
                      add_new_let_in_type prefix let_in_type typ_id
                    in
                    let* typ_args =
                      type_params |> Monad.List.map Type.of_type_expr_variable
                    in
                    let* typ = Type.of_type_expr_without_free_vars typ in
                    let typ_with_let_in_type =
                      apply_let_in_type let_in_type
                        (Type.FunTyps (typ_args, typ))
                    in
                    return
                      ([ TypSynonym (name, typ_with_let_in_type) ], let_in_type)
                | typs ->
                    let* rev_typs, let_in_type =
                      Monad.List.fold_left
                        (fun (rev_typs, let_in_type) typ ->
                          let* name, let_in_type =
                            add_new_let_in_type prefix let_in_type typ.typ_id
                          in
                          return (TypExistential name :: rev_typs, let_in_type))
                        ([], let_in_type) typs
                    in
                    raise
                      (List.rev rev_typs, let_in_type)
                      NotSupported
                      "Mutual type definitions in signatures not handled.")
            | Tsig_typext _ -> return ([], let_in_type)
            | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
                let* prefixed_name =
                  Name.of_strings true (prefix @ [ Ident.name val_id ])
                in
                let* typ = Type.of_type_expr_without_free_vars ctyp_type in
                let typ_args =
                  Type.typ_args_of_typ typ |> Name.Set.elements
                  |> List.map (fun typ -> (typ, 0))
                in
                let typ_with_let_in_type =
                  apply_let_in_type let_in_type
                    (Type.ForallTyps (typ_args, typ))
                in
                return
                  ([ Value (prefixed_name, typ_with_let_in_type) ], let_in_type))))
  in
  match items with
  | [] -> return []
  | item :: items ->
      let next_env =
        match items with { sig_env; _ } :: _ -> sig_env | _ -> last_env
      in
      let* first_items, let_in_type = of_signature_item item next_env in
      let* last_items = of_signature_items prefix let_in_type items last_env in
      return (first_items @ last_items)

let of_signature (signature : signature) : t Monad.t =
  push_env
    (let* items =
       of_signature_items [] [] signature.sig_items signature.sig_final_env
     in
     ModuleTypParams.get_signature_typ_params_arity signature.sig_type
     >>= fun typ_params ->
     let* typ_params =
       Tree.flatten typ_params
       |> Monad.List.map (fun (path, arity) ->
              let* name = Name.of_strings false path in
              return (name, arity))
     in
     return { items; typ_params })

let to_coq_prefixed_name (prefix : Name.t list) (name : Name.t) : SmartPrint.t =
  separate !^"_" (List.map Name.to_coq (prefix @ [ name ]))

let rec to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^("(* " ^ message ^ " *)")
  | Documentation message -> !^("(** " ^ message ^ " *)")
  | Module (name, typ) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")
  | ModuleWithSignature items -> separate newline (to_coq_items items)
  | TypExistential name ->
      nest (Name.to_coq name ^^ !^":=" ^^ Name.to_coq name ^-^ !^";")
  | TypSynonym (name, typ) ->
      nest (Name.to_coq name ^^ !^":=" ^^ Type.to_coq None None typ ^-^ !^";")
  | Value (name, typ) ->
      nest (Name.to_coq name ^^ !^":" ^^ Type.to_coq None None typ ^-^ !^";")

and to_coq_items (items : item list) : SmartPrint.t list =
  List.map to_coq_item items

let to_coq_definition (fargs : FArgs.t) (name : Name.t) (signature : t) :
    SmartPrint.t =
  !^"Module" ^^ Name.to_coq name ^-^ !^"." ^^ newline
  ^^ indent
       (nest
          (!^"Record" ^^ !^"signature" ^^ FArgs.to_coq fargs
          ^^ Type.to_coq_grouped_typ_params Type.Braces signature.typ_params
          ^^ nest (!^":" ^^ Pp.set)
          ^^ !^":=" ^^ !^"{" ^^ newline
          ^^ indent (separate newline (to_coq_items signature.items))
          ^^ newline ^^ !^"}" ^-^ !^"."))
  ^^ newline ^^ !^"End" ^^ Name.to_coq name ^-^ !^"." ^^ newline
  ^^ nest
       (!^"Definition" ^^ Name.to_coq name ^^ !^":="
       ^^ (match signature.typ_params with [] -> empty | _ :: _ -> !^"@")
       ^-^ Name.to_coq name ^-^ !^"." ^-^ !^"signature" ^-^ !^".")
  ^^
  match signature.typ_params with
  | [] -> empty
  | _ :: _ ->
      newline
      ^^ nest
           (!^"Arguments" ^^ Name.to_coq name
           ^^ nest
                (braces
                   (separate space
                      (FArgs.to_coq_underscores fargs
                      @ Pp.n_underscores (List.length signature.typ_params))))
           ^-^ !^".")
