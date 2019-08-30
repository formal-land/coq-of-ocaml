(** A structure represents the contents of a ".ml" file. *)
open Types
open Typedtree
open Sexplib.Std
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = Exp.t Exp.Definition.t
    [@@deriving sexp]

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : t) : SmartPrint.t =
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
type t =
  | Value of Value.t
  | TypeDefinition of TypeDefinition.t
  | Open of Open.t
  | Module of Name.t * t list
  | Signature of Name.t * Signature.t
  [@@deriving sexp]

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : t list =
  let of_structure_item (item : structure_item) : t option =
    let env = Envaux.env_of_only_summary item.str_env in
    let loc = Loc.of_location item.str_loc in
    match item.str_desc with
    | Tstr_value (is_rec, cases) ->
      let def = Exp.import_let_fun loc Name.Map.empty is_rec cases in
      Some (Value def)
    | Tstr_type (_, typs) ->
      let def = TypeDefinition.of_ocaml env loc typs in
      Some (TypeDefinition def)
    | Tstr_exception _ ->
      Error.raise loc (
        "The definition of exception is not handled.\n\n" ^
        "You could use sum types (\"option\", \"result\", ...) to represent error cases, " ^
        "or avoid importing this part of the code."
      )
    | Tstr_open { open_path = path } ->
      let o = Open.of_ocaml loc path in
      Some (Open o)
    | Tstr_module {
        mb_id = name;
        mb_expr = {
          mod_desc = Tmod_structure structure;
          mod_type
        }
      }
    | Tstr_module {
        mb_id = name;
        mb_expr = {
          mod_desc = Tmod_constraint ({ mod_desc = Tmod_structure structure }, _, _, _);
          mod_type
        }
      } ->
      let name = Name.of_ident name in
      begin match IsFirstClassModule.is_module_typ_first_class env loc mod_type with
      | None ->
        let structures = of_structure structure in
        Some (Module (name, structures))
      | Some signature_path ->
        let module_value = Exp.of_structure signature_path structure in
        Some (Value {
          is_rec = Recursivity.New false;
          cases = [
            (
              {
                name;
                typ_vars = [];
                args = [];
                typ = None
              },
              module_value
            )
          ]
        })
      end
    | Tstr_modtype { mtd_type = None } ->
      Error.raise loc "Abstract module types not handled."
    | Tstr_modtype { mtd_id; mtd_type = Some { mty_desc } } ->
      let name = Name.of_ident mtd_id in
      begin
        match mty_desc with
        | Tmty_signature signature ->
          let signature = Signature.of_signature env loc signature in
          Some (Signature (name, signature))
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
    (* We ignore attribute fields. *)
    | Tstr_attribute _ -> None in
  structure.str_items |> Util.List.filter_map of_structure_item

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : t list) : SmartPrint.t =
  let to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.to_coq value
    | TypeDefinition typ_def -> TypeDefinition.to_coq typ_def
    | Open o -> Open.to_coq o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".")
    | Signature (name, signature) -> Signature.to_coq_definition name signature in
  separate (newline ^^ newline) (List.map to_coq_one defs)
