(** An OCaml signature which will by transformed into a dependent record. *)
open SmartPrint
open Typedtree

type item =
  | Typ of Name.t
  | Value of Name.t * Type.t

type t = item list

let pp_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Typ name ->
    group (!^ "Type" ^^ Name.pp name)
  | Value (name, typ) ->
    group (!^ "Value" ^^ Name.pp name ^^ Type.pp typ)

let pp (signature : t) : SmartPrint.t =
  separate newline (List.map pp_item signature)

let of_signature (env : unit FullEnvi.t) (signature : signature) : t =
  let of_signature_item (env : unit FullEnvi.t) (signature_item : signature_item) : unit FullEnvi.t * item =
    let loc = Loc.of_location signature_item.sig_loc in
    match signature_item.sig_desc with
    | Tsig_attribute _ -> Error.raise loc "Structure item `attribute` not handled."
    | Tsig_class _ -> Error.raise loc "Structure item `class` not handled."
    | Tsig_class_type _ -> Error.raise loc "Structure item `class_type` not handled."
    | Tsig_exception _ -> Error.raise loc "Structure item `exception` not handled."
    | Tsig_include _ -> Error.raise loc "Structure item `include` not handled."
    | Tsig_modtype _ -> Error.raise loc "Structure item `modtype` not handled."
    | Tsig_module _ -> Error.raise loc "Structure item `module` not handled."
    | Tsig_open _ -> Error.raise loc "Structure item `open` not handled."
    | Tsig_recmodule _ -> Error.raise loc "Structure item `recmodule` not handled."
    | Tsig_type (_, [{ typ_id }]) ->
      let name = Name.of_ident typ_id in
      let env = FullEnvi.add_typ [] name env in
      (env, Typ name)
    | Tsig_type (_, _) -> Error.raise loc "Mutual type definitions in signatures not handled."
    | Tsig_typext _ -> Error.raise loc "Structure item `typext` not handled."
    | Tsig_value { val_id; val_desc = { ctyp_type } } ->
      let name = Name.of_ident val_id in
      let env = FullEnvi.add_var [] name () env in
      (env, Value (name, Type.of_type_expr env loc ctyp_type)) in
  let (_, items) =
    List.fold_left (fun (env, items) signature_item ->
      let (env, item) = of_signature_item env signature_item in
      (env, item :: items)
    ) (env, []) signature.sig_items in
  List.rev items

let to_coq_item (signature_item : item) : SmartPrint.t =
  match signature_item with
  | Typ name -> Name.to_coq name ^^ !^ ":" ^^ !^ "Type" ^-^ !^ ";"
  | Value (name, typ) -> Name.to_coq name ^^ !^ ":" ^^ Type.to_coq false typ ^-^ !^ ";"

let to_coq (signature : t) : SmartPrint.t =
  group (separate newline (List.map to_coq_item signature))
