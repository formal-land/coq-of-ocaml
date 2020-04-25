(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open SmartPrint
open Monad.Notations

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = Exp.t option Exp.Definition.t

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : t) : SmartPrint.t =
    match value.Exp.Definition.cases with
    | [] -> empty
    | _ :: _ ->
      separate (newline ^^ newline) (value.Exp.Definition.cases |> List.mapi (fun index (header, e) ->
        let firt_case = index = 0 in
        nest (
          begin if firt_case then
            begin if Recursivity.to_bool value.Exp.Definition.is_rec then
              !^ "Fixpoint"
            else
              !^ "Definition"
            end
          else
            !^ "with"
          end ^^
          let { Exp.Header.name; typ_vars; args; typ; _ } = header in
          Name.to_coq name ^^
          begin match typ_vars with
          | [] -> empty
          | _ :: _ ->
            braces @@ group (separate space (List.map Name.to_coq typ_vars) ^^
            !^ ":" ^^ Pp.set)
          end ^^
          group (separate space (args |> List.map (fun (x, t) ->
            parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None t)
          ))) ^^
          Exp.Header.to_coq_structs header ^^
          begin match typ with
          | None -> empty
          | Some typ -> !^ ": " ^-^ Type.to_coq None None typ
          end ^-^
          !^ (match typ with None -> ":=" | _ -> " :=") ^^
          begin match e with
          | None -> !^ "axiom"
          | Some e -> Exp.to_coq false e
          end
        )
      )) ^-^ !^ "."
end

(** A structure. *)
type t =
  | Value of Value.t
  | AbstractValue of Name.t * Name.t list * Type.t
  | TypeDefinition of TypeDefinition.t
  | Open of Open.t
  | Module of Name.t * t list
  | ModuleExp of Name.t * Exp.t
  | ModuleInclude of PathName.t
  | ModuleSynonym of Name.t * PathName.t
  | Signature of Name.t * Signature.t
  | Error of string
  | ErrorMessage of string * t

let error_message
  (structure : t)
  (category : Error.Category.t)
  (message : string)
  : t list Monad.t =
  raise [ErrorMessage (message, structure)] category message

let top_level_evaluation_error : t list Monad.t =
  error_message
    (Error "top_level_evaluation")
    SideEffect
    "Top-level evaluations are ignored"

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : t list Monad.t =
  let of_structure_item (item : structure_item) (final_env : Env.t)
    : t list Monad.t =
    set_env item.str_env (
    set_loc (Loc.of_location item.str_loc) (
    match item.str_desc with
    | Tstr_value (_, [ {
        vb_pat = {
          pat_desc =
            Tpat_construct (
              _,
              { cstr_res = { desc = Tconstr (path, _, _); _ }; _ },
              _
            );
          _
        };
        _
      } ])
      when PathName.is_unit path ->
      top_level_evaluation_error
    | Tstr_eval _ -> top_level_evaluation_error
    | Tstr_value (is_rec, cases) ->
      push_env (
      Exp.import_let_fun Name.Map.empty true is_rec cases >>= fun def ->
      return [Value def])
    | Tstr_type (_, typs) ->
      (* Because types may be recursive, so we need the types to already be in
         the environment. This is useful for example for the detection of
         phantom types. *)
      set_env final_env (
      TypeDefinition.of_ocaml typs >>= fun def ->
      return [TypeDefinition def])
    | Tstr_exception { tyexn_constructor = { ext_id; _ }; _ } ->
      error_message (Error ("exception " ^ Ident.name ext_id)) SideEffect (
        "The definition of exceptions is not handled.\n\n" ^
        "Alternative: using sum types (\"option\", \"result\", ...) to " ^
        "represent error cases."
      )
    | Tstr_open { open_expr; _ } ->
      begin match open_expr with
      | { mod_desc = Tmod_ident (path, _); _ } ->
        Open.of_ocaml path >>= fun o ->
        return [Open o]
      | _ ->
        raise
          [Error "open_module_expression"]
          NotSupported
          "We do not support open on complex module expressions"
      end
    | Tstr_module { mb_id; mb_expr; _ } ->
      let* name = Name.of_ident false mb_id in
      IsFirstClassModule.is_module_typ_first_class mb_expr.mod_type
        >>= fun is_first_class ->
      begin match is_first_class with
      | Found _ ->
        Exp.of_module_expr
          Name.Map.empty mb_expr (Some mb_expr.mod_type) >>= fun module_exp ->
        return [ModuleExp (name, module_exp)]
      | Not_found reason ->
        of_module_expr name mb_expr >>= fun module_expr ->
        begin match module_expr with
        | Some module_expr -> return [module_expr]
        | None ->
          raise
            []
            FirstClassModule
            (
              "We expected to find a signature name for this module.\n\n" ^
              "Reason:\n" ^ reason
            )
        end
      end
    | Tstr_modtype { mtd_type = None; _ } ->
      error_message
        (Error "abstract_module_type")
        NotSupported
        "Abstract module types not handled."
    | Tstr_modtype { mtd_id; mtd_type = Some { mty_desc; _ }; _ } ->
      let* name = Name.of_ident false mtd_id in
      begin
        match mty_desc with
        | Tmty_signature signature ->
          Signature.of_signature signature >>= fun signature ->
          return [Signature (name, signature)]
        | _ ->
          error_message
            (Error "unhandled_module_type")
            NotSupported
            "This kind of signature is not handled."
      end
    | Tstr_primitive { val_id; val_val = { val_type; _ }; _ } ->
      let* name = Name.of_ident true val_id in
      Type.of_typ_expr true Name.Map.empty val_type >>= fun (typ, _, free_typ_vars) ->
      return [AbstractValue (name, Name.Set.elements free_typ_vars, typ)]
    | Tstr_typext _ ->
      error_message
        (Error "type_extension")
        NotSupported
        "Structure item `typext` not handled."
    | Tstr_recmodule _ ->
      error_message
        (Error "recursive_module")
        NotSupported
        "Structure item `recmodule` not handled."
    | Tstr_class _ ->
      error_message
        (Error "class")
        NotSupported
        "Structure item `class` not handled."
    | Tstr_class_type _ ->
      error_message
        (Error "class_type")
        NotSupported
        "Structure item `class_type` not handled."
    | Tstr_include {
        incl_mod = { mod_desc = Tmod_ident (path, _); mod_type; _ };
        _
      }
    | Tstr_include {
        incl_mod = {
          mod_desc = Tmod_constraint ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _);
          mod_type;
          _
        };
        _
      } ->
      PathName.of_path_with_convert false path >>= fun reference ->
      IsFirstClassModule.is_module_typ_first_class mod_type
        >>= fun is_first_class ->
      begin match is_first_class with
      | IsFirstClassModule.Found mod_type_path ->
        get_env >>= fun env ->
        begin match Mtype.scrape env mod_type with
        | Mty_ident path | Mty_alias path ->
          error_message
            (Error "include_module_with_abstract_module_type")
            NotSupported
            (
              "Cannot get the fields of the abstract module type `" ^
              Path.name path ^ "` to handle the include."
            )
        | Mty_signature signature ->
          signature |> Monad.List.filter_map (fun signature_item ->
            match signature_item with
            | Types.Sig_value (ident, _, _) | Sig_type (ident, _, _, _) ->
              let is_value =
                match signature_item with
                | Types.Sig_value _ -> true
                | _ -> false in
              let* name = Name.of_ident is_value ident in
              PathName.of_path_and_name_with_convert mod_type_path name
                >>= fun field ->
              return (Some (
                ModuleExp (
                  name,
                  Exp.Variable (
                    MixedPath.Access (
                      reference,
                      [field],
                      false
                    ),
                    []
                  )
                )
              ))
            | _ -> return None
          )
        | Mty_functor _ ->
          error_message
            (Error "include_functor")
            Unexpected
            "Unexpected include of functor."
        end
      | IsFirstClassModule.Not_found _ ->
        return [ModuleInclude reference]
      end
    | Tstr_include _ ->
      error_message
        (Error "include")
        NotSupported
        (
          "Cannot include this kind of module expression.\n\n" ^
          "Try to first give a name to this module."
        )
    (* We ignore attribute fields. *)
    | Tstr_attribute _ -> return [])) in
  Monad.List.fold_right
    (fun structure_item (structure, final_env) ->
      let env = structure_item.str_env in
      of_structure_item structure_item final_env >>= fun structure_item ->
      return (structure_item @ structure, env)
    )
    structure.str_items
    ([], structure.str_final_env) >>= fun (structure, _) ->
  return structure

and of_module_expr (name : Name.t) (module_expr : module_expr)
  : t option Monad.t =
  match module_expr.mod_desc with
  | Tmod_structure structure ->
    of_structure structure >>= fun structures ->
    return (Some (Module (name, structures)))
  | Tmod_ident (path, _) ->
    PathName.of_path_with_convert false path >>= fun reference ->
    return (Some (ModuleSynonym (name, reference)))
  | Tmod_apply _ | Tmod_functor _ ->
    Exp.of_module_expr Name.Map.empty module_expr None >>= fun module_exp ->
    return (Some (ModuleExp (name, module_exp)))
  | Tmod_constraint (module_expr, _, _, _) -> of_module_expr name module_expr
  | Tmod_unpack _ -> return None

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : t list) : SmartPrint.t =
  let rec to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.to_coq value
    | AbstractValue (name, typ_vars, typ) ->
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_vars with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^
        nest (parens (separate space (typ_vars |> List.map Name.to_coq) ^^ !^ ":" ^^ Pp.set)) ^-^ !^ ","
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
    | ModuleExp (name, e) ->
      let (e, typ) =
        match e with
        | TypeAnnotation (e, typ) -> (e, Some typ)
        | _ -> (e, None) in
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^
        begin match typ with
        | None -> empty
        | Some typ -> !^ ":" ^^ Type.to_coq None None typ
        end ^^
        !^ ":=" ^^
        Exp.to_coq false e ^-^ !^ "."
      )
    | ModuleInclude reference ->
      nest (!^ "Include" ^^ PathName.to_coq reference ^-^ !^ ".")
    | ModuleSynonym (name, reference) ->
      nest (!^ "Module" ^^ Name.to_coq name ^^ !^ ":=" ^^ PathName.to_coq reference ^-^ !^ ".")
    | Signature (name, signature) -> Signature.to_coq_definition name signature
    | Error message -> !^ ( "(* " ^ message ^ " *)")
    | ErrorMessage (message, def) ->
      nest (
        Error.to_comment message ^^ newline ^^
        to_coq_one def
      ) in
  separate (newline ^^ newline) (defs |> List.map to_coq_one)
