(** An OCaml signature which will by transformed into a dependent record. *)
open Sexplib.Std
open SmartPrint
open Typedtree

type item =
  | Module of Name.t * ModuleTyp.t
  | TypExistential of Name.t
  | TypSynonym of Name.t * Name.t list * Type.t
  | Value of Name.t * Name.t list * Type.t
  [@@deriving sexp]

type t = {
  items: item list;
  typ_params: Name.t list }
  [@@deriving sexp]

let of_signature (env : FullEnvi.t) (signature : signature) : t =
  let of_signature_item (env : FullEnvi.t) (signature_item : signature_item) : FullEnvi.t * item =
    let loc = Loc.of_location signature_item.sig_loc in
    match signature_item.sig_desc with
    | Tsig_attribute _ -> Error.raise loc "Signature item `attribute` not handled."
    | Tsig_class _ -> Error.raise loc "Signature item `class` not handled."
    | Tsig_class_type _ -> Error.raise loc "Signature item `class_type` not handled."
    | Tsig_exception _ -> Error.raise loc "Signature item `exception` not handled."
    | Tsig_include _ -> Error.raise loc "Signature item `include` not handled."
    | Tsig_modtype _ -> Error.raise loc "Signatures inside signatures are not handled."
    | Tsig_module { md_id; md_type } ->
      let name = Name.of_ident md_id in
      let module_typ = ModuleTyp.of_ocaml env md_type in
      let env = FullEnvi.add_first_class_module [] name env in
      (env, Module (name, module_typ))
    | Tsig_open _ -> Error.raise loc "Signature item `open` not handled."
    | Tsig_recmodule _ -> Error.raise loc "Recursive module signatures are not handled."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = None; type_params = [] } } ]) ->
      let name = Name.of_ident typ_id in
      let env = FullEnvi.add_typ [] name env in
      (env, TypExistential name)
    | Tsig_type (_, [ { typ_type = { type_manifest = None; type_params = _ :: _ } } ]) ->
      Error.raise loc "Polymorphic existential types not handled in signatures."
    | Tsig_type (_, [ { typ_id; typ_type = { type_manifest = Some typ; type_params } } ]) ->
      let name = Name.of_ident typ_id in
      let env = FullEnvi.add_typ [] name env in
      let typ_args = type_params |> List.map (fun typ_param ->
        Type.of_type_expr_variable loc typ_param
      ) in
      let typ = Type.of_type_expr env loc typ in
      (env, TypSynonym (name, typ_args, typ))
    | Tsig_type (_, _) -> Error.raise loc "Mutual type definitions in signatures not handled."
    | Tsig_typext _ -> Error.raise loc "Extensible types are not handled."
    | Tsig_value { val_id; val_desc = { ctyp_desc; ctyp_type } } ->
      let name = Name.of_ident val_id in
      let env = FullEnvi.add_var [] name env in
      let typ = Type.of_type_expr env loc ctyp_type in
      let typ_args = Name.Set.elements (Type.typ_args typ) in
      (env, Value (name, typ_args, typ)) in
  let (_, items, typ_params) =
    List.fold_left (fun (env, items, typ_params) signature_item ->
      let (env, item) = of_signature_item env signature_item in
      (
        env,
        item :: items,
        match item with
        | TypExistential typ -> typ :: typ_params
        | _ -> typ_params
      )
    ) (env, [], []) signature.sig_items in
  { items = List.rev items; typ_params = List.rev typ_params }

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Module (name, module_typ) ->
    Name.to_coq name ^^ !^ ":" ^^ ModuleTyp.to_coq module_typ
  | TypExistential name -> Name.to_coq name ^^ !^ ":=" ^^ Name.to_coq name
  | TypSynonym (name, typ_args, typ) ->
    Name.to_coq name ^^
    (match typ_args with
    | [] -> empty
    | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type")) ^^
    !^ ":=" ^^ Type.to_coq false typ
  | Value (name, typ_args, typ) ->
    Name.to_coq name ^^ !^ ":" ^^
    (match typ_args with
    | [] -> empty
    | _ :: _ ->
      !^ "forall" ^^ braces (group (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
    Type.to_coq false typ

let to_coq_definition (name : Name.t) (signature : t) : SmartPrint.t =
  nest (
    !^ "Record" ^^ Name.to_coq name ^^
    (match signature.typ_params with
    | [] -> empty
    | _ ->
      !^ "(" ^-^
      separate space (List.map (fun typ_param -> !^ typ_param) signature.typ_params) ^^
      !^ ":" ^^ !^ "Type" ^-^ !^ ")"
    ) ^^
    !^ ":=" ^^ !^ "{" ^^ newline ^^
    indent (separate newline (List.map (fun item -> to_coq_item item ^-^ !^ ";") signature.items)) ^^ newline ^^
    !^ "}" ^-^ !^ ".")
