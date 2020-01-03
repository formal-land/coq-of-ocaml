(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open SmartPrint
open Monad.Notations

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = Exp.t Exp.Definition.t

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : t) : SmartPrint.t =
    match value.Exp.Definition.cases with
    | [] -> empty
    | _ :: _ ->
      separate (newline ^^ newline) (value.Exp.Definition.cases |> List.mapi (fun index (header, e) ->
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
            parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None t)))) ^^
          (match header.Exp.Header.typ with
          | None -> empty
          | Some typ -> !^ ": " ^-^ Type.to_coq None None typ) ^-^
          !^ " :=" ^^ Exp.to_coq false e))) ^-^ !^ "."
end

(** A structure. *)
type t =
  | Eval of Exp.t
  | Value of Value.t
  | AbstractValue of Name.t * Name.t list * Type.t
  | TypeDefinition of TypeDefinition.t
  | Open of Open.t
  | Module of Name.t * t list
  | ModuleInclude of PathName.t
  | ModuleSynonym of Name.t * PathName.t
  | Signature of Name.t * Signature.t
  | Error of string
  | ErrorMessage of string * t

let error_message (structure : t) (category : Error.Category.t) (message : string) : t option Monad.t =
  raise (Some (ErrorMessage (message, structure))) category message

let top_level_evaluation (e : expression) : t option Monad.t =
  Exp.of_expression Name.Map.empty e >>= fun e ->
    error_message
      (Eval e)
      SideEffect
      "Top-level evaluations are considered as an error as sources of side-effects"

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : t list Monad.t =
  let of_structure_item (item : structure_item) : t option Monad.t =
    set_env item.str_env (
    set_loc (Loc.of_location item.str_loc) (
    match item.str_desc with
    | Tstr_value (_, [ {
        vb_pat = {
          pat_desc = Tpat_construct (_, { cstr_res = { desc = Tconstr (path, _, _); _ }; _ }, _);
          _
        };
        vb_expr = e;
        _
      } ])
      when PathName.is_unit (PathName.of_path_without_convert path) ->
      top_level_evaluation e
    | Tstr_eval (e, _) -> top_level_evaluation e
    | Tstr_value (is_rec, cases) ->
      Exp.import_let_fun Name.Map.empty is_rec cases >>= fun def ->
      return (Some (Value def))
    | Tstr_type (_, typs) ->
      TypeDefinition.of_ocaml typs >>= fun def ->
      return (Some (TypeDefinition def))
    | Tstr_exception _ ->
      error_message (Error "exception") SideEffect (
        "The definition of exceptions is not handled.\n\n" ^
        "Alternative: using sum types (\"option\", \"result\", ...) to represent error cases."
      )
    | Tstr_open open_description ->
      let o = Open.of_ocaml open_description in
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
    | Tstr_module {
        mb_id = name;
        mb_expr = {
          mod_desc = Tmod_ident (_, long_ident);
          _
        };
        _
      } ->
      let name = Name.of_ident name in
      let reference = PathName.of_long_ident long_ident.txt in
      return (Some (ModuleSynonym (name, reference)))
    | Tstr_module { mb_expr = { mod_desc = Tmod_functor _; _ }; _ } ->
      error_message (Error "functor") NotSupported "Functors are not handled."
    | Tstr_module { mb_expr = { mod_desc = Tmod_apply _; _ }; _ } ->
      error_message (Error "functor_application") NotSupported "Applications of functors are not handled."
    | Tstr_module _ -> error_message (Error "unhandled_module") NotSupported "This kind of module is not handled."
    | Tstr_modtype { mtd_type = None; _ } ->
      error_message (Error "abstract_module_type") NotSupported "Abstract module types not handled."
    | Tstr_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ } ->
      let name = Name.of_ident mtd_id in
      begin
        match mty_desc with
        | Tmty_signature signature ->
          Signature.of_signature signature >>= fun signature ->
          return (Some (Signature (name, signature)))
        | _ -> error_message (Error "unhandled_module_type") NotSupported "This kind of signature is not handled."
      end
    | Tstr_primitive { val_id; val_val = { val_type; _ }; _ } ->
      let name = Name.of_ident val_id in
      Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, free_typ_vars) ->
      return (Some (AbstractValue (name, Name.Set.elements free_typ_vars, typ)))
    | Tstr_typext _ -> error_message (Error "type_extension") NotSupported "Structure item `typext` not handled."
    | Tstr_recmodule _ -> error_message (Error "recursive_module") NotSupported "Structure item `recmodule` not handled."
    | Tstr_class _ -> error_message (Error "class") NotSupported "Structure item `class` not handled."
    | Tstr_class_type _ -> error_message (Error "class_type") NotSupported "Structure item `class_type` not handled."
    | Tstr_include { incl_mod = { mod_desc = Tmod_ident (_, long_ident); _ }; _ }
    | Tstr_include {
        incl_mod = {
          mod_desc = Tmod_constraint ({ mod_desc = Tmod_ident (_, long_ident); _ }, _, _, _);
          _
        };
        _
      } ->
      let reference = PathName.of_long_ident long_ident.txt in
      return (Some (ModuleInclude reference))
    | Tstr_include _ ->
      error_message (Error "include") NotSupported "Cannot include this kind of module expression"
    (* We ignore attribute fields. *)
    | Tstr_attribute _ -> return None)) in
  structure.str_items |> Monad.List.filter_map of_structure_item

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : t list) : SmartPrint.t =
  let rec to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Eval e -> !^ "Compute" ^^ Exp.to_coq false e ^-^ !^ "."
    | Value value -> Value.to_coq value
    | AbstractValue (name, typ_vars, typ) ->
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_vars with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^
        nest (parens (separate space (typ_vars |> List.map Name.to_coq) ^^ !^ ":" ^^ !^ "Type")) ^-^ !^ ","
      ) ^^
      Type.to_coq None None typ ^-^ !^ "."
    | TypeDefinition typ_def -> TypeDefinition.to_coq typ_def
    | Open o -> Open.to_coq o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ "."
      )
    | ModuleInclude reference ->
      nest (!^ "Export" ^^ PathName.to_coq reference ^-^ !^ ".")
    | ModuleSynonym (name, reference) ->
      nest (!^ "Module" ^^ Name.to_coq name ^^ !^ ":=" ^^ PathName.to_coq reference ^-^ !^ ".")
    | Signature (name, signature) -> Signature.to_coq_definition name signature
    | Error message -> !^ message
    | ErrorMessage (message, def) ->
      nest (
        Error.to_comment message ^^ newline ^^
        to_coq_one def
      ) in
  separate (newline ^^ newline) (defs |> List.map to_coq_one)
