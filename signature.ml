open Typedtree
open SmartPrint

(** The declaration of a value. *)
module Value = struct
  type t = {
    name : Name.t;
    typ_args : Name.t list;
    typ : Type.t }

  let pp (value : t) : SmartPrint.t =
    nest (!^ "Value" ^^ OCaml.tuple [
      Name.pp value.name; OCaml.list Name.pp value.typ_args; Type.pp value.typ])

(*   let depth_lift (value : t) : t =
    { value with typ = Type.depth_lift value.typ }
 *)
  let leave_prefix (x : Name.t) (value : t) : t =
    { value with typ = Type.leave_prefix x value.typ }

  let of_ocaml (env : (unit, 's) FullEnvi.t) (loc : Loc.t)
    (value : value_description) : t =
    let name = Name.of_ident value.val_id in
    let typ = Type.of_type_expr env loc value.val_desc.ctyp_type in
    let typ_args = Type.typ_args typ in
    { name = name;
      typ_args = Name.Set.elements typ_args;
      typ = typ }

  let update_env (value : t) (v : 'a) (env : ('a, 's) FullEnvi.t)
    : ('a, 's) FullEnvi.t =
    FullEnvi.add_var [] value.name v env

  let to_coq (value : t) : SmartPrint.t =
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

type t =
  | Declaration of Loc.t * Value.t
  | TypeDefinition of Loc.t * TypeDefinition.t

let rec pp (decls : t list) : SmartPrint.t =
  separate (newline ^^ newline) (decls |> List.map (function
    | Declaration (loc, value) ->
      group (Loc.pp loc ^^ OCaml.tuple [Value.pp value])
    | TypeDefinition (loc, typ_def) ->
      group (Loc.pp loc ^^ TypeDefinition.pp typ_def)))

(*let rec depth_lift (decls : t list) : t list =
  decls |> List.map (function
    | Declaration (loc, value) -> Declaration (loc, Value.depth_lift value)
    | Module (loc, name, decls) -> Module (loc, name, depth_lift decls))*)

let rec leave_prefix (x : Name.t) (decls : t list) : t list =
  decls |> List.map (function
    | Declaration (loc, value) -> Declaration (loc, Value.leave_prefix x value)
    | TypeDefinition (loc, typ_def) -> failwith "TODO")

let of_signature_item (env : (unit, 's) FullEnvi.t) (item : signature_item)
  : (unit, 's) FullEnvi.t * t =
  let loc = Loc.of_location item.sig_loc in
  match item.sig_desc with
  | Tsig_value declaration ->
    let declaration = Value.of_ocaml env loc declaration in
    let env = Value.update_env declaration () env in
    (env, Declaration (loc, declaration))
  | Tsig_type typs ->
    let typ_def = TypeDefinition.of_ocaml env loc typs in
    let env = TypeDefinition.update_env typ_def env in
    (env, TypeDefinition (loc, typ_def))
  | _ -> Error.raise loc "Module type item not handled."

let of_signature (env : (unit, 's) FullEnvi.t) (signature : signature)
  : (unit, 's) FullEnvi.t * t list =
  let env = FullEnvi.enter_module env in
  let (env, decls) =
    List.fold_left (fun (env, decls) item ->
      let (env, decl) = of_signature_item env item in
      (env, decl :: decls))
    (env, []) signature.sig_items in
  (env, List.rev decls)

let update_env (env : ('a, 's) FullEnvi.t) (name : Name.t) (decls : t list)
  : ('a, 's) FullEnvi.t =
  FullEnvi.add_signature [] name decls env

let to_coq_one (decl : t) : SmartPrint.t =
  match decl with
  | Declaration (_, value) -> Value.to_coq value
  | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def

let rec to_coq (decls : t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map to_coq_one decls)