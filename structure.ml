(** A structure represents the contents of a ".ml" file. *)
open Types
open Typedtree
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type 'a t = 'a Exp.t Exp.Definition.t

  let pp (pp_a : 'a -> SmartPrint.t) (value : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ Exp.Definition.pp (Exp.pp pp_a) value)
  
  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : 'a t) : SmartPrint.t =
    let firt_case = ref true in
    separate (newline ^^ newline) (value.Exp.Definition.cases |> List.map (fun (header, e) ->
      nest (
        (if !firt_case then (
          firt_case := false;
          if Recursivity.to_bool value.Exp.Definition.is_rec then
            !^ "Fixpoint"
          else
            !^ "Definition"
        ) else
          !^ "with") ^^
        Name.to_coq header.Exp.Header.name ^^
        (match header.Exp.Header.typ_vars with
        | [] -> empty
        | _ :: _ ->
          braces @@ group (separate space (List.map Name.to_coq header.Exp.Header.typ_vars) ^^
          !^ ":" ^^ !^ "Type")) ^^
        group (separate space (header.Exp.Header.args |> List.map (fun (x, t) ->
          parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false t)))) ^^
        (match header.Exp.Header.typ with
        | None -> empty
        | Some typ -> !^ ": " ^-^ Type.to_coq false typ) ^-^
        !^ " :=" ^^ Exp.to_coq false e))) ^-^ !^ "."
end

(** A structure. *)
type 'a t =
  | Value of Loc.t * 'a Value.t
  | TypeDefinition of Loc.t * TypeDefinition.t
  | Exception of Loc.t * Exception.t
  | Reference of Loc.t * Reference.t
  | Open of Loc.t * Open.t
  | Module of Loc.t * Name.t * 'a t list
  | Signature of Loc.t * Name.t * 'a Signature.t list

let rec pps (pp_a : 'a -> SmartPrint.t) (defs : 'a t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map (pp pp_a) defs)

and pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
  match def with
  | Value (loc, value) ->
    group (Loc.pp loc ^^ Value.pp pp_a value)
  | TypeDefinition (loc, typ_def) ->
    group (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Exception (loc, exn) -> group (Loc.pp loc ^^ Exception.pp exn)
  | Reference (loc, r) -> group (Loc.pp loc ^^ Reference.pp r)
  | Open (loc, o) -> group (Loc.pp loc ^^ Open.pp o)
  | Module (loc, name, defs) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps pp_a defs))
  | Signature (loc, name, decls) ->
    nest (
      Loc.pp loc ^^ !^ "Signature" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (Signature.pps pp_a decls))

(** Import an OCaml structure. *)
let rec of_structure (env : (unit, unit Signature.t) FullEnvi.t)
  (structure : structure) : (unit, unit Signature.t) FullEnvi.t * Loc.t t list =
  let of_structure_item (env : (unit, 's) FullEnvi.t) (item : structure_item)
    : (unit, 's) FullEnvi.t * Loc.t t =
    let loc = Loc.of_location item.str_loc in
    match item.str_desc with
    | Tstr_value (_, cases) when Reference.is_reference loc cases ->
      let r = Reference.of_ocaml env loc cases in
      let env = Reference.update_env r env in
      (env, Reference (loc, r))
    | Tstr_value (is_rec, cases) ->
      let (env, def) =
        Exp.import_let_fun env loc Name.Map.empty is_rec cases in
      (env, Value (loc, def))
    | Tstr_type typs ->
      let def = TypeDefinition.of_ocaml env loc typs in
      let env = TypeDefinition.update_env def env in
      (env, TypeDefinition (loc, def))
    | Tstr_exception exn ->
      let exn = Exception.of_ocaml env loc exn in
      let env = Exception.update_env exn env in
      (env, Exception (loc, exn))
    | Tstr_open (_, path, _, _) ->
      let o = Open.of_ocaml loc path in
      let env = Open.update_env o env in
      (env, Open (loc, o))
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc = Tmod_structure structure }}
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc =
        Tmod_constraint ({ mod_desc = Tmod_structure structure }, _, _, _) }} ->
      let name = Name.of_ident name in
      let env = FullEnvi.enter_module env in
      let (env, structures) = of_structure env structure in
      let env = FullEnvi.leave_module name env in
      (env, Module (loc, name, structures))
    | Tstr_modtype { mtd_id = name; mtd_type = Some { mty_desc = Tmty_signature
      signature } } ->
      let name = Name.of_ident name in
      let (_, decls) = Signature.of_signature env signature in
      let unit_decls = Signature.map (fun _ -> ()) decls in
      let env = Signature.update_env env name unit_decls in
      (env, Signature (loc, name, decls))
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc = Tmod_functor (_, _,
      { mty_desc = Tmty_ident (signature_name, _) },
      { mod_desc = Tmod_structure structure }) }} ->
      Error.raise loc "Functors not handled."
    | _ -> Error.raise loc "Structure item not handled." in
  let (env, defs) =
    List.fold_left (fun (env, defs) item ->
      let (env, def) = of_structure_item env item in
      (env, def :: defs))
    (env, []) structure.str_items in
  (env, List.rev defs)

let rec monadise_let_rec (env : (unit, unit Signature.t) FullEnvi.t)
  (defs : Loc.t t list) : (unit, unit Signature.t) FullEnvi.t * Loc.t t list =
  let rec monadise_let_rec_one (env : (unit, 's) FullEnvi.t) (def : Loc.t t)
    : (unit, 's) FullEnvi.t * Loc.t t list =
    match def with
    | Value (loc, def) ->
      let (env, defs) = Exp.monadise_let_rec_definition env def in
      (env, defs |> List.rev |> List.map (fun def -> Value (loc, def)))
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def env, [def])
    | Exception (loc, exn) -> (Exception.update_env exn env, [def])
    | Reference (loc, r) -> (Reference.update_env r env, [def])
    | Open (loc, o) -> (Open.update_env o env, [def])
    | Module (loc, name, defs) ->
      let env = FullEnvi.enter_module env in
      let (env, defs) = monadise_let_rec env defs in
      let env = FullEnvi.leave_module name env in
      (env, [Module (loc, name, defs)])
    | Signature (loc, name, decls) ->
      let unit_decls = Signature.map (fun _ -> ()) decls in
      let env = Signature.update_env env name unit_decls in
      (env, [Signature (loc, name, decls)]) in
  let (env, defs) = List.fold_left (fun (env, defs) def ->
    let (env, defs') = monadise_let_rec_one env def in
    (env, defs' @ defs))
    (env, []) defs in
  (env, List.rev defs)

let rec effects (env : (Effect.Type.t, Effect.Type.t Signature.t) FullEnvi.t)
  (defs : 'a t list)
  : (Effect.Type.t, Effect.Type.t Signature.t) FullEnvi.t *
    ('a * Effect.t) t list =
  let rec effects_one (env : (Effect.Type.t, 's) FullEnvi.t) (def : 'a t)
    : (Effect.Type.t, 's) FullEnvi.t * ('a * Effect.t) t =
    match def with
    | Value (loc, def) ->
      let def = Exp.effects_of_def env def in
      (if def.Exp.Definition.cases |> List.exists (fun (header, e) ->
        header.Exp.Header.args = [] &&
          not (Effect.Descriptor.is_pure (snd (Exp.annotation e)).Effect.descriptor)) then
        Error.warn loc "Toplevel effects are forbidden.");
      let env = Exp.env_after_def_with_effects env def in
      (env, Value (loc, def))
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def env, TypeDefinition (loc, typ_def))
    | Exception (loc, exn) ->
      let id = Effect.Descriptor.Id.Loc loc in
      (Exception.update_env_with_effects exn env id, Exception (loc, exn))
    | Reference (loc, r) ->
      let id = Effect.Descriptor.Id.Loc loc in
      (Reference.update_env_with_effects r env id, Reference (loc, r))
    | Open (loc, o) -> (Open.update_env o env, Open (loc, o))
    | Module (loc, name, defs) ->
      let env = FullEnvi.enter_module env in
      let (env, defs) = effects env defs in
      let env = FullEnvi.leave_module name env in
      (env, Module (loc, name, defs))
    | Signature (loc, name, decls) ->
      let decls = Signature.effects decls in
      let effects_decls = Signature.map snd decls in
      let env = Signature.update_env env name effects_decls in
      (env, Signature (loc, name, decls)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env, def) =
        effects_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

let rec monadise (env : (unit, 's) FullEnvi.t) (defs : (Loc.t * Effect.t) t list)
  : (unit, 's) FullEnvi.t * Loc.t t list =
  let rec monadise_one (env : (unit, 's) FullEnvi.t) (def : (Loc.t * Effect.t) t)
    : (unit, 's) FullEnvi.t * Loc.t t =
    match def with
    | Value (loc, def) ->
      let env_in_def = Exp.Definition.env_in_def def env in
      let def = { def with
        Exp.Definition.cases =
          def.Exp.Definition.cases |> List.map (fun (header, e) ->
            let typ = match header.Exp.Header.typ with
            | Some typ -> Some (Type.monadise typ (snd (Exp.annotation e)))
            | None -> None in
        let header = { header with Exp.Header.typ = typ } in
        let env = Exp.Header.env_in_header header env_in_def () in
        let e = Exp.monadise env e in
        (header, e)) } in
      let env = Exp.Definition.env_after_def def env in
      (env, Value (loc, def))
    | TypeDefinition (loc, typ_def) ->
      (TypeDefinition.update_env typ_def env, TypeDefinition (loc, typ_def))
    | Exception (loc, exn) ->
      (Exception.update_env exn env, Exception (loc, exn))
    | Reference (loc, r) -> (Reference.update_env r env, Reference (loc, r))
    | Open (loc, o) -> (Open.update_env o env, Open (loc, o))
    | Module (loc, name, defs) ->
      let (env, defs) = monadise (FullEnvi.enter_module env) defs in
      (FullEnvi.leave_module name env, Module (loc, name, defs))
    | Signature (loc, name, decls) ->
      let decls = Signature.monadise decls in
      let env = Signature.update_env env name decls in
      (env, Signature (loc, name, decls)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env_units, def) = monadise_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : 'a t list) : SmartPrint.t =
  let to_coq_one (def : 'a t) : SmartPrint.t =
    match def with
    | Value (_, value) -> Value.to_coq value
    | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def
    | Exception (_, exn) -> Exception.to_coq exn
    | Reference (_, r) -> Reference.to_coq r
    | Open (_, o) -> Open.to_coq o
    | Module (_, name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".")
    | Signature (_, name, decls) ->
      nest (
        !^ "Module Type" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (Signature.to_coq decls) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)
