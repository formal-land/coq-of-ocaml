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
  | Open of Loc.t * Open.t
  | Module of Loc.t * Name.t * 'a t list
  | Signature of Loc.t * Name.t * Signature.t

let rec pps (pp_a : 'a -> SmartPrint.t) (defs : 'a t list) : SmartPrint.t =
  separate (newline ^^ newline) (List.map (pp pp_a) defs)

and pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
  match def with
  | Value (loc, value) ->
    group (Loc.pp loc ^^ Value.pp pp_a value)
  | TypeDefinition (loc, typ_def) ->
    group (Loc.pp loc ^^ TypeDefinition.pp typ_def)
  | Open (loc, o) -> group (Loc.pp loc ^^ Open.pp o)
  | Module (loc, name, defs) ->
    nest (
      Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (pps pp_a defs))
  | Signature (loc, name, signature) ->
    nest (
      Loc.pp loc ^^ !^ "Signature" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (Signature.pp signature))

(** Import an OCaml structure. *)
let rec of_structure (env : unit FullEnvi.t) (structure : structure)
  : unit FullEnvi.t * Loc.t t list =
  let of_structure_item (env : unit FullEnvi.t) (item : structure_item)
    : unit FullEnvi.t * Loc.t t =
    let loc = Loc.of_location item.str_loc in
    match item.str_desc with
    | Tstr_value (is_rec, cases) ->
      let (env, def) =
        Exp.import_let_fun env loc Name.Map.empty is_rec cases in
      (env, Value (loc, def))
    | Tstr_type (_, typs) ->
      let def = TypeDefinition.of_ocaml env loc typs in
      let env = TypeDefinition.update_env def env in
      (env, TypeDefinition (loc, def))
    | Tstr_exception _ ->
      Error.raise loc (
        "The definition of exception is not handled.\n\n" ^
        "You could use sum types (\"option\", \"result\", ...) to represent error cases, " ^
        "or avoid importing this part of the code."
      )
    | Tstr_open { open_path = path } ->
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
    | Tstr_modtype { mtd_type = None } -> Error.raise loc "Abstract module types not handled."
    | Tstr_modtype { mtd_id; mtd_type = Some { mty_desc } } ->
      let name = Name.of_ident mtd_id in
      begin
        match mty_desc with
        | Tmty_signature signature -> (env, Signature (loc, name, Signature.of_signature env signature))
        | _ -> Error.raise loc "This kind of signature is not handled."
      end
    | Tstr_module { mb_expr = { mod_desc = Tmod_functor _ }} ->
      Error.raise loc "Functors not handled."
    | Tstr_module _ -> Error.raise loc "This kind of module is not handled."
    | Tstr_eval _ -> Error.raise loc "Structure item `eval` not handled."
    | Tstr_primitive _ -> Error.raise loc "Structure item `primitive` not handled."
    | Tstr_typext _ -> Error.raise loc "Structure item `typext` not handled."
    | Tstr_recmodule _ -> Error.raise loc "Structure item `recmodule` not handled."
    | Tstr_class _ -> Error.raise loc "Structure item `class` not handled."
    | Tstr_class_type _ -> Error.raise loc "Structure item `class_type` not handled."
    | Tstr_include _ -> Error.raise loc "Structure item `include` not handled."
    | Tstr_attribute _ -> Error.raise loc "Structure item `attribute` not handled." in
  let (env, defs) =
    List.fold_left (fun (env, defs) item ->
      (* We ignore attribute items. *)
      match item.str_desc with
      | Tstr_attribute _ -> (env, defs)
      | _ ->
        let (env, def) = of_structure_item env item in
        (env, def :: defs))
    (env, []) structure.str_items in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : 'a t list) : SmartPrint.t =
  let to_coq_one (def : 'a t) : SmartPrint.t =
    match def with
    | Value (_, value) -> Value.to_coq value
    | TypeDefinition (_, typ_def) -> TypeDefinition.to_coq typ_def
    | Open (_, o) -> Open.to_coq o
    | Module (_, name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".")
    | Signature (_, name, signature) ->
      nest (
        !^ "Record" ^^ Name.to_coq name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
        indent (Signature.to_coq signature) ^^ newline ^^
        !^ "}" ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)
