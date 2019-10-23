(** An OCaml signature which will by transformed into a dependent record. *)
open Sexplib.Std
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Module of Name.t * ModuleTyp.t
  | TypExistential of Name.t
  | TypSynonym of Name.t * Name.t list * Type.t
  | Value of Name.t * Name.t list * Type.t
  [@@deriving sexp]

type t = {
  items: item list;
  typ_params: unit Tree.t }
  [@@deriving sexp]

let of_signature (signature : signature) : t Monad.t =
  let of_signature_item (signature_item : signature_item) : item Monad.t =
    set_env signature_item.sig_env (
    set_loc (Loc.of_location signature_item.sig_loc) (
    match signature_item.sig_desc with
    | Tsig_attribute _ ->
      raise (Error "attribute") NotSupported "Signature item `attribute` not handled."
    | Tsig_class _ ->
      raise (Error "class") NotSupported "Signature item `class` not handled."
    | Tsig_class_type _ ->
      raise (Error "class_type") NotSupported "Signature item `class_type` not handled."
    | Tsig_exception _ ->
      raise (Error "exception") SideEffect "Signature item `exception` not handled."
    | Tsig_include _ ->
      raise (Error "include") NotSupported "Signature item `include` not handled."
    | Tsig_modtype _ ->
      raise (Error "module_type") NotSupported "Signatures inside signatures are not handled."
    | Tsig_module { md_id; md_type } ->
      let name = Name.of_ident md_id in
      ModuleTyp.of_ocaml md_type >>= fun module_typ ->
      return (Module (name, module_typ))
    | Tsig_open _ ->
      raise (Error "open") NotSupported "Signature item `open` not handled."
    | Tsig_recmodule _ ->
      raise (Error "recursive_module") NotSupported "Recursive module signatures are not handled."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = None; type_params = [] } } ]) ->
      let name = Name.of_ident typ_id in
      return (TypExistential name)
    | Tsig_type (_, [ { typ_type = { type_manifest = None; type_params = _ :: _ } } ]) ->
      raise
        (Error "polymorphic_abstract_type")
        NotSupported
        "Polymorphic abstract types not handled in signatures."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = Some typ; type_params } } ]) ->
      let name = Name.of_ident typ_id in
      (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (TypSynonym (name, typ_args, typ))
    | Tsig_type (_, _) ->
      raise (Error "mutual_type") NotSupported "Mutual type definitions in signatures not handled."
    | Tsig_typext _ ->
      raise (Error "extensible_type") NotSupported "Extensible types are not handled."
    | Tsig_value { val_id; val_desc = { ctyp_desc; ctyp_type } } ->
      let name = Name.of_ident val_id in
      Type.of_type_expr_without_free_vars ctyp_type >>= fun typ ->
      let typ_args = Name.Set.elements (Type.typ_args typ) in
      return (Value (name, typ_args, typ)))) in
  (signature.sig_items |> Monad.List.map of_signature_item) >>= fun items ->
  (ModuleTypParams.get_signature_typ_params signature.sig_type) >>= fun typ_params ->
  return { items; typ_params }

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^ message
  | Module (name, module_typ) ->
    Name.to_coq name ^^ !^ ":" ^^ ModuleTyp.to_coq name module_typ
  | TypExistential name -> Name.to_coq name ^^ !^ ":=" ^^ Name.to_coq name
  | TypSynonym (name, typ_args, typ) ->
    Name.to_coq name ^^
    (match typ_args with
    | [] -> empty
    | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type")) ^^
    !^ ":=" ^^ Type.to_coq None false typ
  | Value (name, typ_args, typ) ->
    Name.to_coq name ^^ !^ ":" ^^
    (match typ_args with
    | [] -> empty
    | _ :: _ ->
      !^ "forall" ^^ braces (group (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
    Type.to_coq None false typ

let to_coq_definition (name : Name.t) (signature : t) : SmartPrint.t =
  let typ_params : Name.t list =
    Tree.flatten signature.typ_params |> List.map (fun (path_name, _) ->
      ModuleTypParams.get_typ_param_name path_name
    ) in
  !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
  indent (
    nest (
      !^ "Record" ^^ !^ "signature" ^^
      (match typ_params with
      | [] -> empty
      | _ -> braces (separate space (typ_params |> List.map Name.to_coq) ^^ !^ ":" ^^ !^ "Type")
      ) ^^
      !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate newline (List.map (fun item -> to_coq_item item ^-^ !^ ";") signature.items)) ^^ newline ^^
      !^ "}" ^-^ !^ "."
    ) ^^
    (match typ_params with
    | [] -> empty
    | _ ->
      newline ^^ !^ "Arguments" ^^ !^ "signature" ^^ !^ ":" ^^ !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
    )
  ) ^^ newline ^^
  !^ "End" ^^ Name.to_coq name ^-^ !^ "."
