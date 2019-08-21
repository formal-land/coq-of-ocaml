(** An OCaml signature which will by transformed into a dependent record. *)
open Sexplib.Std
open SmartPrint
open Typedtree

type item =
  | Value of Name.t * Name.t list * Type.t
  [@@deriving sexp]

type t = {
  items: item list;
  typ_params: Name.t list }
  [@@deriving sexp]

type item_or_typ =
  | Item of item
  | Typ of Name.t

let of_signature (env : FullEnvi.t) (signature : signature) : t =
  let of_signature_item (env : FullEnvi.t) (signature_item : signature_item) : FullEnvi.t * item_or_typ =
    let loc = Loc.of_location signature_item.sig_loc in
    match signature_item.sig_desc with
    | Tsig_attribute _ -> Error.raise loc "Signature item `attribute` not handled."
    | Tsig_class _ -> Error.raise loc "Signature item `class` not handled."
    | Tsig_class_type _ -> Error.raise loc "Signature item `class_type` not handled."
    | Tsig_exception _ -> Error.raise loc "Signature item `exception` not handled."
    | Tsig_include _ -> Error.raise loc "Signature item `include` not handled."
    | Tsig_modtype _ -> Error.raise loc "Signature item `modtype` not handled."
    | Tsig_module _ -> Error.raise loc "Signature item `module` not handled."
    | Tsig_open _ -> Error.raise loc "Signature item `open` not handled."
    | Tsig_recmodule _ -> Error.raise loc "Signature item `recmodule` not handled."
    | Tsig_type (_, [{ typ_id; typ_params = [] }]) ->
      let name = Name.of_ident typ_id in
      let env = FullEnvi.add_typ [] name env in
      (env, Typ name)
    | Tsig_type (_, [{ typ_params = _ :: _ }]) ->
      Error.raise loc "Polymorphic types not handled in signatures."
    | Tsig_type (_, _) -> Error.raise loc "Mutual type definitions in signatures not handled."
    | Tsig_typext _ -> Error.raise loc "Signature item `typext` not handled."
    | Tsig_value { val_id; val_desc = { ctyp_desc; ctyp_type } } ->
      let name = Name.of_ident val_id in
      let env = FullEnvi.add_var [] name env in
      let typ = Type.of_type_expr env loc ctyp_type in
      let typ_args = Name.Set.elements (Type.typ_args typ) in
      (env, Item (Value (name, typ_args, typ))) in
  let (_, (items, typ_params)) =
    List.fold_left (fun (env, (items, typ_params)) signature_item ->
      let (env, item_or_typ) = of_signature_item env signature_item in
      (
        env,
        match item_or_typ with
        | Item item -> (item :: items, typ_params)
        | Typ typ -> (items, typ :: typ_params)
      )
    ) (env, ([], [])) signature.sig_items in
  { items = List.rev items; typ_params = List.rev typ_params }

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Value (name, typ_args, typ) ->
    Name.to_coq name ^^ !^ ":" ^^
    (match typ_args with
    | [] -> empty
    | _ :: _ ->
      !^ "forall" ^^ braces (group (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
    Type.to_coq false typ ^-^ !^ ";"

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
    indent (separate newline (List.map to_coq_item signature.items)) ^^ newline ^^
    !^ "}" ^-^ !^ ".")
