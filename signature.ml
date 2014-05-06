open Typedtree
open SmartPrint

(** The declaration of a value. *)
module Value = struct
  type 'a t = {
    annotation : 'a;
    name : Name.t;
    typ_args : Name.t list;
    typ : Type.t }

  let pp (pp_a : 'a -> SmartPrint.t) (declaration : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ OCaml.tuple [
      pp_a declaration.annotation; Name.pp declaration.name;
      OCaml.list Name.pp declaration.typ_args; Type.pp declaration.typ])

  let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
    (declaration : value_description) : Loc.t t =
    let name = Name.of_ident declaration.val_id in
    let typ = declaration.val_desc.ctyp_type in
    let (typ, _, typ_args) =
      Type.of_type_expr_new_typ_vars env loc Name.Map.empty typ in
    { annotation = loc;
      name = name;
      typ_args = Name.Set.elements typ_args;
      typ = typ }

  let update_env (f : 'a -> 'b) (declaration : 'a t) (env : 'b FullEnvi.t)
    : 'b FullEnvi.t =
    FullEnvi.add_var [] declaration.name (f declaration.annotation) env
end

type 'a t =
  | Declaration of Loc.t * 'a Value.t
  | TypeDefinition of Loc.t * TypeDefinition.t
  | Exception of Loc.t * Exception.t
  | Reference of Loc.t * Reference.t
  | Open of Loc.t * Open.t
  | Module of Loc.t * Name.t * 'a t list

let rec pps (pp_a : 'a -> SmartPrint.t) (decls : 'a t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map (pp pp_a) decls)

and pp (pp_a : 'a -> SmartPrint.t) (decl : 'a t) : SmartPrint.t =
  match decl with
  | Declaration (loc, value) ->
    nest (Loc.pp loc ^^ OCaml.tuple [Value.pp pp_a value])
  | TypeDefinition (loc, typ_def) ->
    nest (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Exception (loc, exn) -> nest (Loc.pp loc ^^ Exception.pp exn)
  | Reference (loc, r) -> nest (Loc.pp loc ^^ Reference.pp r)
  | Open (loc, o) -> nest (Loc.pp loc ^^ Open.pp o)
  | Module (loc, name, decls) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps pp_a decls))

let rec of_signature (env : unit FullEnvi.t) (signature : signature)
  : unit FullEnvi.t * Loc.t t list =
  let (env, decls) =
    List.fold_left (fun (env, decls) item ->
      let (env, decl) = of_signature_item env item in
      (env, decl :: decls))
    (env, []) signature.sig_items in
  (env, List.rev decls)

and of_signature_item (env : unit FullEnvi.t) (item : signature_item)
  : unit FullEnvi.t * Loc.t t =
  let loc = Loc.of_location item.sig_loc in
  match item.sig_desc with
  | Tsig_value declaration ->
    let declaration = Value.of_ocaml env loc declaration in
    let env = Value.update_env (fun _ -> ()) declaration env in
    (env, Declaration (loc, declaration))
  | Tsig_type typs ->
    let typ_def = TypeDefinition.of_ocaml env loc typs in
    let env = TypeDefinition.update_env typ_def env in
    (env, TypeDefinition (loc, typ_def))
  | Tsig_exception exn ->
    let exn = Exception.of_ocaml env loc exn in
    let env = Exception.update_env exn env in
    (env, Exception (loc, exn))
  | Tsig_open (_, path, _, _) ->
    let o = Open.of_ocaml loc path in
    let env = Open.update_env o env in
    (env, Open (loc, o))
  (*| Tsig_module { md_id = name; md_type = } ->
    let name = Name.of_ident name in
    let env = FullEnvi.enter_module env in
    let (env, structures) = of_structure env structure in
    let env = FullEnvi.leave_module name env in
    (env, Module (loc, name, structures))*)
  | _ -> Error.raise loc "Module type item not handled."

let update_env (env : 'a FullEnvi.t) (name : Name.t) (defs : 'b t list)
  : 'a FullEnvi.t =
  env
