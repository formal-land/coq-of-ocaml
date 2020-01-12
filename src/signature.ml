(** An OCaml signature which will by transformed into a dependent record. *)
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Module of Name.t * ModuleTyp.t
  | TypExistential of Name.t * Name.t list
  | TypSynonym of Name.t * Name.t list * Type.t
  | Value of Name.t * Name.t list * Type.t

type t = {
  items: item list;
  typ_params: ModuleTypParams.t }

let items_of_types_signature (signature : Types.signature) : item list Monad.t =
  let of_types_signature_item (signature_item : Types.signature_item)
    : item Monad.t =
    match signature_item with
    | Sig_value (ident, { val_type; _ }) ->
      let name = Name.of_ident true ident in
      Type.of_type_expr_without_free_vars val_type >>= fun typ ->
      let typ_args = Name.Set.elements (Type.typ_args typ) in
      return (Value (name, typ_args, typ))
    | Sig_type (ident, { type_manifest = None; type_params; _ }, _) ->
      let name = Name.of_ident false ident in
      Monad.List.map Type.of_type_expr_variable type_params >>= fun typ_args ->
      return (TypExistential (name, typ_args))
    | Sig_type (ident, { type_manifest = Some typ; type_params; _ }, _) ->
      let name = Name.of_ident false ident in
      Monad.List.map Type.of_type_expr_variable type_params >>= fun typ_args ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (TypSynonym (name, typ_args, typ))
    | Sig_typext (_, { ext_type_path; _ }, _) ->
      let name = Path.name ext_type_path in
      raise
        (Error ("extensible_type " ^ name))
        NotSupported
        ("Extensible type '" ^ name ^ "' not handled")
    | Sig_module (ident, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("module " ^ name))
        NotSupported
        (
          "Module '" ^ name ^ "' in included signature not handled.\n\n" ^
          "You may try to use a sub-module instead of an `include`."
        )
    | Sig_modtype (ident, _) ->
      let name = Ident.name ident in
      raise
        (Error ("module_type" ^ name))
        NotSupported
        ("Signatures '" ^ name ^ "' inside signature is not handled")
    | Sig_class (ident, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class" ^ name))
        NotSupported
        ("Class '" ^ name ^ "' not handled.")
    | Sig_class_type (ident, _, _) ->
      let name = Ident.name ident in
      raise
        (Error ("class_type" ^ name))
        NotSupported
        ("Class type '" ^ name ^ "' not handled.") in
  signature |> Monad.List.map of_types_signature_item

let of_types_signature (signature : Types.signature) : t Monad.t =
  items_of_types_signature signature >>= fun items ->
  (ModuleTypParams.get_signature_typ_params signature) >>= fun typ_params ->
  return { items; typ_params }

let items_of_signature (signature : signature) : item list Monad.t =
  let of_signature_item (signature_item : signature_item) : item list Monad.t =
    set_env signature_item.sig_env (
    set_loc (Loc.of_location signature_item.sig_loc) (
    match signature_item.sig_desc with
    | Tsig_attribute _ -> return []
    | Tsig_class _ ->
      raise [Error "class"] NotSupported "Signature item `class` not handled."
    | Tsig_class_type _ ->
      raise
        [Error "class_type"]
        NotSupported
        "Signature item `class_type` not handled."
    | Tsig_exception _ ->
      raise
        [Error "exception"]
        SideEffect
        "Signature item `exception` not handled."
    | Tsig_include { incl_type; _ } -> items_of_types_signature incl_type
    | Tsig_modtype _ ->
      raise
        [Error "module_type"]
        NotSupported
        "Signatures inside signatures are not handled."
    | Tsig_module { md_id; md_type; _ } ->
      let name = Name.of_ident false md_id in
      ModuleTyp.of_ocaml md_type >>= fun module_typ ->
      return [Module (name, module_typ)]
    | Tsig_open _ ->
      raise [Error "open"] NotSupported "Signature item `open` not handled."
    | Tsig_recmodule _ ->
      raise [Error "recursive_module"] NotSupported "Recursive module signatures are not handled."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = None; type_params; _ }; _ } ]) ->
      let name = Name.of_ident false typ_id in
      (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      return [TypExistential (name, typ_args)]
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = Some typ; type_params; _ }; _ } ]) ->
      let name = Name.of_ident false typ_id in
      (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return [TypSynonym (name, typ_args, typ)]
    | Tsig_type (_, _) ->
      raise [Error "mutual_type"] NotSupported "Mutual type definitions in signatures not handled."
    | Tsig_typext { tyext_path; _ } ->
      raise
      [Error ("extensible_type " ^ Path.name tyext_path)]
        NotSupported
        "Extensible types are not handled."
    | Tsig_value { val_id; val_desc = { ctyp_type; _ }; _ } ->
      let name = Name.of_ident true val_id in
      Type.of_type_expr_without_free_vars ctyp_type >>= fun typ ->
      let typ_args = Name.Set.elements (Type.typ_args typ) in
      return [Value (name, typ_args, typ)])) in
  (signature.sig_items |> Monad.List.map of_signature_item) >>= fun items ->
  return (List.flatten items)

let of_signature (signature : signature) : t Monad.t =
  set_scoping_env (
  items_of_signature signature >>= fun items ->
  ModuleTypParams.get_signature_typ_params signature.sig_type >>= fun typ_params ->
  return { items; typ_params })

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Error message -> !^ ("(* " ^ message ^ " *)")
  | Module (name, module_typ) ->
    nest (Name.to_coq name ^^ !^ ":" ^^ ModuleTyp.to_coq name module_typ ^-^ !^ ";")
  | TypExistential (name, _) ->
    nest (Name.to_coq name ^^ !^ ":=" ^^ Name.to_coq name ^-^ !^ ";")
  | TypSynonym (name, typ_args, typ) ->
    nest (
      Name.to_coq name ^^
      (match typ_args with
      | [] -> empty
      | _ ->
        parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set)
      ) ^^ !^ ":=" ^^ Type.to_coq None None typ ^-^ !^ ";"
    )
  | Value (name, typ_args, typ) ->
    nest (
      Name.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ Pp.set)) ^-^ !^ ",") ^^
      Type.to_coq None None typ ^-^ !^ ";"
    )

let rec to_coq_type_kind (arity : int) : SmartPrint.t =
  if arity = 0 then
    Pp.set
  else
    Pp.set ^^ !^ "->" ^^ to_coq_type_kind (arity - 1)

let to_coq_definition (name : Name.t) (signature : t) : SmartPrint.t =
  let typ_params : (Name.t * int) list =
    Tree.flatten signature.typ_params |> List.map (fun (path_name, arity) ->
      (ModuleTypParams.get_typ_param_name path_name, arity)
    ) in
  let reversed_grouped_typ_params : (Name.t list * int) list =
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
          separate space (typ_params |> List.map Name.to_coq) ^^ !^ ":" ^^
          to_coq_type_kind arity
        )
      )) ^^
      !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate newline (List.map to_coq_item signature.items)) ^^ newline ^^
      !^ "}" ^-^ !^ "."
    ) ^^
    (match typ_params with
    | [] -> empty
    | _ ->
      newline ^^ !^ "Arguments" ^^ !^ "signature" ^^ !^ ":" ^^ !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
    )
  ) ^^ newline ^^
  !^ "End" ^^ Name.to_coq name ^-^ !^ "."
