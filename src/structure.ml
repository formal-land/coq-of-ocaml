(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open Sexplib.Std
open SmartPrint
open Monad.Notations

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = Exp.t Exp.Definition.t
    [@@deriving sexp]

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : t) : SmartPrint.t option =
    match value.Exp.Definition.cases with
    | [] -> None
    | _ :: _ ->
      Some (separate (newline ^^ newline) (value.Exp.Definition.cases |> List.mapi (fun index (header, e) ->
        let firt_case = index = 0 in
        nest (
          (if firt_case then (
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
            parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None false t)))) ^^
          (match header.Exp.Header.typ with
          | None -> empty
          | Some typ -> !^ ": " ^-^ Type.to_coq None false typ) ^-^
          !^ " :=" ^^ Exp.to_coq false e))) ^-^ !^ ".")
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
let rec of_structure (structure : structure) : t list Monad.t =
  let of_structure_item (item : structure_item) : t option Monad.t =
    set_env item.str_env (
    set_loc (Loc.of_location item.str_loc) (
    match item.str_desc with
    | Tstr_value (is_rec, cases) ->
      Exp.import_let_fun Name.Map.empty is_rec cases >>= fun def ->
      return (Some (Value def))
    | Tstr_type (_, typs) ->
      TypeDefinition.of_ocaml typs >>= fun def ->
      return (Some (TypeDefinition def))
    | Tstr_exception _ ->
      raise None SideEffect (
        "The definition of exceptions is not handled.\n\n" ^
        "Alternative: using sum types (\"option\", \"result\", ...) to represent error cases."
      )
    | Tstr_open { open_path = path; _ } ->
      let o = Open.of_ocaml path in
      return (Some (Open o))
    | Tstr_module {
        mb_id = name;
        mb_expr = {
          mod_desc = Tmod_structure structure;
          _
        };
        _
      }
    | Tstr_module {
        mb_id = name;
        mb_expr = {
          mod_desc = Tmod_constraint ({ mod_desc = Tmod_structure structure; _ }, _, _, _);
          _
        };
        _
      } ->
      let name = Name.of_ident name in
      of_structure structure >>= fun structures ->
      return (Some (Module (name, structures)))
    | Tstr_modtype { mtd_type = None; _ } ->
      raise None NotSupported "Abstract module types not handled."
    | Tstr_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ } ->
      let name = Name.of_ident mtd_id in
      begin
        match mty_desc with
        | Tmty_signature signature ->
          Signature.of_signature signature >>= fun signature ->
          return (Some (Signature (name, signature)))
        | _ -> raise None NotSupported "This kind of signature is not handled."
      end
    | Tstr_module { mb_expr = { mod_desc = Tmod_functor _; _ }; _ } ->
      raise None NotSupported "Functors are not handled."
    | Tstr_module { mb_expr = { mod_desc = Tmod_apply _; _ }; _ } ->
      raise None NotSupported "Applications of functors are not handled."
    | Tstr_module _ -> raise None NotSupported "This kind of module is not handled."
    | Tstr_eval _ -> raise None SideEffect "Top-level evaluations are not handled"
    | Tstr_primitive _ -> raise None NotSupported "Structure item `primitive` not handled."
    | Tstr_typext _ -> raise None NotSupported "Structure item `typext` not handled."
    | Tstr_recmodule _ -> raise None NotSupported "Structure item `recmodule` not handled."
    | Tstr_class _ -> raise None NotSupported "Structure item `class` not handled."
    | Tstr_class_type _ -> raise None NotSupported "Structure item `class_type` not handled."
    | Tstr_include _ -> raise None NotSupported "Structure item `include` not handled."
    (* We ignore attribute fields. *)
    | Tstr_attribute _ -> return None)) in
  structure.str_items |> Monad.List.filter_map of_structure_item

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : t list) : SmartPrint.t =
  let to_coq_one (def : t) : SmartPrint.t option =
    match def with
    | Value value -> Value.to_coq value
    | TypeDefinition typ_def -> Some (TypeDefinition.to_coq typ_def)
    | Open o -> Some (Open.to_coq o)
    | Module (name, defs) ->
      Some (nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ "."))
    | Signature (name, signature) -> Some (Signature.to_coq_definition name signature) in
  separate (newline ^^ newline) (Util.List.filter_map to_coq_one defs)
