open Typedtree
open SmartPrint

(** The declaration of a value. *)
module Value = struct
  type 'a t = {
    annotation : 'a;
    name : Name.t;
    typ_args : Name.t list;
    typ : Type.t }

  let pp (pp_a : 'a -> SmartPrint.t) (value : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ OCaml.tuple [
      pp_a value.annotation; Name.pp value.name;
      OCaml.list Name.pp value.typ_args; Type.pp value.typ])

  let of_ocaml (env : (unit, 's) FullEnvi.t) (loc : Loc.t)
    (value : value_description) : Loc.t t =
    let name = Name.of_ident value.val_id in
    let typ = Type.of_type_expr env loc value.val_desc.ctyp_type in
    let typ_args = Type.typ_args typ in
    { annotation = loc;
      name = name;
      typ_args = Name.Set.elements typ_args;
      typ = typ }

  let update_env (f : 'a -> 'b) (value : 'a t) (env : ('b, 's) FullEnvi.t)
    : ('b, 's) FullEnvi.t =
    FullEnvi.add_var [] value.name (f value.annotation) env

  let effects (value : Loc.t t) : (Loc.t * Effect.t) t =
    { value with annotation = (value.annotation, Effect.pure) }

  let monadise (value : (Loc.t * Effect.t) t) : Loc.t t =
    { value with annotation = fst value.annotation }

  let to_coq (value : 'a t) : SmartPrint.t =
    nest (
      !^ "Parameter" ^^ Name.to_coq value.name ^^ !^ ":" ^^
      (match value.typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq value.typ_args) ^^
          !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      Type.to_coq false value.typ ^-^ !^ ".")
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
    group (Loc.pp loc ^^ OCaml.tuple [Value.pp pp_a value])
  | TypeDefinition (loc, typ_def) ->
    group (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Exception (loc, exn) -> group (Loc.pp loc ^^ Exception.pp exn)
  | Reference (loc, r) -> group (Loc.pp loc ^^ Reference.pp r)
  | Open (loc, o) -> group (Loc.pp loc ^^ Open.pp o)
  | Module (loc, name, decls) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps pp_a decls))

let rec of_signature (env : (unit, 's) FullEnvi.t) (signature : signature)
  : (unit, 's) FullEnvi.t * Loc.t t list =
  let (env, decls) =
    List.fold_left (fun (env, decls) item ->
      let (env, decl) = of_signature_item env item in
      (env, decl :: decls))
    (env, []) signature.sig_items in
  (env, List.rev decls)

and of_signature_item (env : (unit, 's) FullEnvi.t) (item : signature_item)
  : (unit, 's) FullEnvi.t * Loc.t t =
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
  | Tsig_module { md_id = name; md_type = { mty_desc = Tmty_signature
    signature } } ->
    let name = Name.of_ident name in
    let env = FullEnvi.enter_module env in
    let (env, decls) = of_signature env signature in
    let env = FullEnvi.leave_module name env in
    (env, Module (loc, name, decls))
  | _ -> Error.raise loc "Module type item not handled."

let update_env (env : ('a, 's) FullEnvi.t) (name : Name.t) (defs : 'b t list)
  : ('a, 's) FullEnvi.t =
  env

let rec effects (decls : Loc.t t list) : (Loc.t * Effect.t) t list =
  List.map effects_one decls

and effects_one (decl : Loc.t t) : (Loc.t * Effect.t) t =
  match decl with
  | Declaration (loc, value) -> Declaration (loc, Value.effects value)
  | TypeDefinition (loc, typ_def) -> TypeDefinition (loc, typ_def)
  | Exception (loc, exn) -> Exception (loc, exn)
  | Reference (loc, r) -> Reference (loc, r)
  | Open (loc, o) -> Open (loc, o)
  | Module (loc, name, decls) -> Module (loc, name, effects decls)

let rec monadise (decls : (Loc.t * Effect.t) t list) : Loc.t t list =
  List.map monadise_one decls

and monadise_one (decl : (Loc.t * Effect.t) t) : Loc.t t =
  match decl with
  | Declaration (loc, value) -> Declaration (loc, Value.monadise value)
  | TypeDefinition (loc, typ_def) -> TypeDefinition (loc, typ_def)
  | Exception (loc, exn) -> Exception (loc, exn)
  | Reference (loc, r) -> Reference (loc, r)
  | Open (loc, o) -> Open (loc, o)
  | Module (loc, name, decls) -> Module (loc, name, monadise decls)

let rec to_coq (decls : 'a t list) : SmartPrint.t =
  let to_coq_one (decl : 'a t) : SmartPrint.t =
    match decl with
    | Declaration (_, value) -> Value.to_coq value
    | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def
    | Exception (_, exn) -> Exception.to_coq exn
    | Reference (_, r) -> Reference.to_coq r
    | Open (_, o) -> Open.to_coq o
    | Module (_, name, decls) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq decls) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one decls)