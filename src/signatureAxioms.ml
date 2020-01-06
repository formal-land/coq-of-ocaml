(** A signature represented by axioms for a [.mli] file. *)
open SmartPrint
open Typedtree
open Monad.Notations

type item =
  | Error of string
  | Module of Name.t * t
  | TypDefinition of TypeDefinition.t
  | Value of Name.t * Name.t list * Type.t

and t = item list

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
    | Tsig_modtype _ ->
      raise (Some (Error "module_type")) NotSupported "Signatures inside signatures are not handled"
    | Tsig_module { md_id; md_type = { mty_desc = Tmty_signature signature; _ }; _ } ->
      let name = Name.of_ident false md_id in
      of_signature signature >>= fun signature ->
      return (Some (Module (name, signature)))
    | Tsig_module _ ->
      raise (Some (Error "unhandled_module")) NotSupported "This kind of module is not supported in signatures"
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
    | TypDefinition typ_definition -> TypeDefinition.to_coq typ_definition
    | Value (name, typ_vars, typ) ->
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_vars with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq typ_vars) ^^
          !^ ":" ^^ Pp.set)) ^-^ !^ ",") ^^
      Type.to_coq None None typ ^-^ !^ "." in
  separate (newline ^^ newline) (signature |> List.map to_coq_item)
