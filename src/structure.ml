(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open SmartPrint
open Monad.Notations

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = Exp.t option Exp.Definition.t

  let to_coq_typ_vars (header : Exp.Header.t) : SmartPrint.t =
    let { Exp.Header.typ_vars; _ } = header in
    Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
      braces (nest (typ_vars ^^ !^ ":" ^^ Pp.set))
    )

  let to_coq_args (header : Exp.Header.t) : SmartPrint.t =
    let { Exp.Header.args; _ } = header in
    group (separate space (args |> List.map (fun (x, t) ->
      parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None t)
    )))

  let to_coq_notation_synonym (name : Name.t) (typ_vars : Name.t list)
    : SmartPrint.t =
    nest (
      !^ "let" ^^ Name.to_coq name ^^
      Name.to_coq_list_or_empty typ_vars (fun typ_vars -> braces typ_vars) ^^
      !^ ":=" ^^ !^ "'" ^-^ Name.to_coq name ^^
      separate space (List.map Name.to_coq typ_vars) ^^ !^ "in" ^^ newline
    )

  (** Pretty-print a value definition to Coq. *)
  let to_coq (with_args : bool) (value : t) : SmartPrint.t =
    match value.Exp.Definition.cases with
    | [] -> empty
    | _ :: _ ->
      let (axiom_cases, notation_cases, cases) =
        List.fold_right
          (fun case (axiom_cases, notation_cases, cases) ->
            match case with
            | (header, None) -> (header :: axiom_cases, notation_cases, cases)
            | (header, Some e) ->
              if header.Exp.Header.is_notation then
                (axiom_cases, (header, e) :: notation_cases, cases)
              else
                (axiom_cases, notation_cases, (header, e) :: cases)
          )
          value.Exp.Definition.cases
          ([], [], []) in
      separate (newline ^^ newline) (
        (axiom_cases |> List.map (fun header ->
          let { Exp.Header.name; typ_vars; typ; _ } = header in
          nest (
            !^ "Axiom" ^^ Name.to_coq name ^^ !^ ":" ^^
            Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
              !^ "forall" ^^
              braces (nest (typ_vars ^^ !^ ":" ^^ Pp.set)) ^-^ !^ ","
            ) ^^
            Type.to_coq None None typ ^-^
            !^ "."
          )
        )) @
          begin match notation_cases with
          | [] -> []
          | _ :: _ ->
            [separate newline (notation_cases |> List.map (fun (header, _) ->
              let { Exp.Header.name; _ } = header in
              nest (
                !^ "Reserved Notation" ^^
                double_quotes (!^ "'" ^-^ Name.to_coq name) ^-^ !^ "."
              )
            ))]
          end
        @ (cases |> List.mapi (fun index (header, e) ->
          let first_case = index = 0 in
          let last_case =
            match notation_cases with
            | [] -> index = List.length cases - 1
            | _ :: _ -> false in
          nest (
            begin if first_case then
              begin if value.Exp.Definition.is_rec then
                !^ "Fixpoint"
              else
                !^ "Definition"
              end
            else
              !^ "with"
            end ^^
            let { Exp.Header.name; typ; _ } = header in
            Name.to_coq name ^^
            Pp.args with_args ^^
            to_coq_typ_vars header ^^
            to_coq_args header ^^
            Exp.Header.to_coq_structs header ^^
            !^ ": " ^-^ Type.to_coq None None typ ^-^ !^ " :=" ^^
            group (
              separate space (notation_cases |> List.map (fun (header, e) ->
                let { Exp.Header.name; typ_vars; _ } = header in
                to_coq_notation_synonym name typ_vars
              )) ^^
              Exp.to_coq false e
             ) ^-^
            begin if last_case then
              !^"."
            else
              empty
            end
          )
        )) @ snd (List.fold_left
          (fun ((index, previous_notations), definitions) (header, e) ->
            let first_case = index = 0 in
            let last_case = index = List.length notation_cases - 1 in
            let { Exp.Header.name; typ_vars; structs; typ; _ } = header in
            let definition = nest (
              begin if first_case then
                !^ "where"
              else
                !^ "and"
              end ^^
              double_quotes (!^ "'" ^-^ Name.to_coq name) ^^
              !^ ":=" ^^
              parens (nest (
                nest (
                  Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
                    nest (
                      !^ "fun" ^^ parens (typ_vars ^^ !^ ":" ^^ Pp.set) ^^
                      !^ "=>"
                    ) ^^ space
                  ) ^-^
                  begin match structs with
                  | [] -> !^ "fun"
                  | _ :: _ -> !^ "fix" ^^ Name.to_coq name
                  end ^^
                  to_coq_args header ^^
                  begin match structs with
                  | [] -> !^ "=>"
                  | _ :: _ ->
                    Exp.Header.to_coq_structs header ^^
                    !^ ": " ^-^ Type.to_coq None None typ ^-^ !^ " :="
                  end ^^
                  group (
                    separate space (previous_notations |> List.map (fun (name, typ_vars) ->
                      to_coq_notation_synonym name typ_vars
                    )) ^^
                    Exp.to_coq false e
                  )
                )
              )) ^-^
              begin if last_case then
                !^ "."
              else
                empty
              end
            ) in
            (
              (index + 1, previous_notations @ [(name, typ_vars)]),
              definitions @ [definition]
            )
          )
          ((0, []), [])
          notation_cases
        ) @
          begin match notation_cases with
          | [] -> []
          | _ :: _ ->
            [separate newline (notation_cases |> List.map (fun (header, _) ->
              let { Exp.Header.name; typ_vars; _ } = header in
              nest (
                !^ "Definition" ^^ Name.to_coq name ^^
                Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
                  braces typ_vars
                ) ^^ !^ ":=" ^^
                separate space (
                  (!^ "'" ^-^ Name.to_coq name) :: List.map Name.to_coq typ_vars
                ) ^-^ !^ "."
              )
            ))]
          end
      )
end

type functor_parameters = ModuleTyp.free_vars * (Name.t * Type.t) list

(** A structure. *)
type t =
  | Value of Value.t
  | AbstractValue of Name.t * Name.t list * Type.t
  | TypeDefinition of TypeDefinition.t
  | Module of
    Name.t *
    functor_parameters *
    t list *
    (Exp.t * Type.t option) option
  | ModuleExpression of Name.t * Type.t option * Exp.t
  | ModuleInclude of PathName.t
  | ModuleIncludeItem of Name.t * Name.t list * MixedPath.t
  | ModuleSynonym of Name.t * PathName.t
  | Signature of Name.t * Signature.t
  | Documentation of string * t list
  | Error of string
  | ErrorMessage of string * t

let error_message
  (structure : t)
  (category : Error.Category.t)
  (message : string)
  : t list Monad.t =
  raise [ErrorMessage (message, structure)] category message

let wrap_documentation (items : t list Monad.t) : t list Monad.t =
  let* documentation = get_documentation in
  match documentation with
  | None -> items
  | Some documentation ->
    let* items = items in
    return [Documentation (documentation, items)]

let top_level_evaluation (e : expression) : t list Monad.t =
  push_env (
  let* e = Exp.of_expression Name.Map.empty e in
  let header = {
    Exp.Header.name = Name.of_string_raw "init_module";
    typ_vars = [];
    args = [];
    structs = [];
    typ = Type.Apply (MixedPath.of_name (Name.of_string_raw "unit"), []);
    is_notation = false;
  } in
  let documentation = "Init function; without side-effects in Coq" in
  return [Documentation (documentation, [Value {
    is_rec = false;
    cases = [(
      header,
      Some e
    )]
  }])])

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : t list Monad.t =
  let get_include_items
    (module_path : Path.t option)
    (reference : PathName.t)
    (mod_type : Types.module_type)
    : t list Monad.t =
    let* is_first_class =
      IsFirstClassModule.is_module_typ_first_class mod_type module_path in
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
        let* items =
          signature |> Monad.List.filter_map (fun signature_item ->
            match signature_item with
            | Types.Sig_value (ident, _, _) | Sig_type (ident, _, _, _) ->
              let is_value =
                match signature_item with
                | Types.Sig_value _ -> true
                | _ -> false in
              let* name = Name.of_ident is_value ident in
              let* field =
                PathName.of_path_and_name_with_convert mod_type_path name in
              let* typ_vars =
                match signature_item with
                | Types.Sig_value (_, { val_type; _ }, _) ->
                  let typ_vars = Name.Map.empty in
                  let* (_, _, new_typ_vars) =
                    Type.of_typ_expr true typ_vars val_type in
                  return (Name.Set.elements new_typ_vars)
                | _ -> return [] in
              return (Some (ModuleIncludeItem (
                name,
                typ_vars,
                MixedPath.Access (reference, [field])
              )))
            | _ -> return None
          ) in
        let documentation =
          "Inclusion of the module [" ^ PathName.to_string reference ^ "]" in
        return [Documentation (documentation, items)]
      | Mty_functor _ ->
        error_message
          (Error "include_functor")
          Unexpected
          "Unexpected include of functor."
      end
    | _ -> return [ModuleInclude reference]
    end in
  let of_structure_item (item : structure_item) (final_env : Env.t)
    : t list Monad.t =
    set_env item.str_env (
    set_loc item.str_loc (
    wrap_documentation (
    match item.str_desc with
    | Tstr_value (_, [ {
        vb_attributes;
        vb_pat = {
          pat_desc =
            Tpat_construct (
              _,
              { cstr_res = { desc = Tconstr (path, _, _); _ }; _ },
              _
            );
          _
        };
        vb_expr;
        _
      } ])
      when PathName.is_unit path ->
      let* attributes = Attribute.of_attributes vb_attributes in
      if Attribute.has_axiom_with_reason attributes then
        return []
      else
        top_level_evaluation vb_expr
    | Tstr_eval (e, _) ->
      top_level_evaluation e
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
    | Tstr_open _ -> return []
    | Tstr_module { mb_id; mb_expr; mb_attributes; _ } ->
      let* name = Name.of_optional_ident false mb_id in
      let* has_plain_module_attribute =
        let* attributes = Attribute.of_attributes mb_attributes in
        return (Attribute.has_plain_module attributes) in
      let* module_definition =
        of_module name ([], []) mb_expr has_plain_module_attribute in
      return [module_definition]
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
        ExtensibleType
        "We do not handle type extensions"
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
      let* reference = PathName.of_path_with_convert false path in
      get_include_items (Some path) reference mod_type
    | Tstr_include { incl_mod; _ } ->
      let* include_name = Exp.get_include_name incl_mod in
      let* module_definition = of_module include_name ([], []) incl_mod false in
      let reference = PathName.of_name [] include_name in
      let* include_items =
        get_include_items None reference incl_mod.mod_type in
      return (module_definition :: include_items)
    (* We ignore attribute fields. *)
    | Tstr_attribute _ -> return []))) in
  Monad.List.fold_right
    (fun structure_item (structure, final_env) ->
      let env = structure_item.str_env in
      of_structure_item structure_item final_env >>= fun structure_item ->
      return (structure_item @ structure, env)
    )
    structure.str_items
    ([], structure.str_final_env) >>= fun (structure, _) ->
  return structure

and of_module
  (name : Name.t)
  (functor_parameters : functor_parameters)
  (module_expr : module_expr) (has_plain_module_attribute : bool)
  : t Monad.t =
  let path =
    match module_expr.mod_desc with
    | Tmod_ident (path, _)
    | Tmod_constraint ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
      Some path
    | _ -> None in
  let* is_first_class =
    IsFirstClassModule.is_module_typ_first_class module_expr.mod_type path in
  let as_expression =
    match (is_first_class, has_plain_module_attribute) with
    | (Found module_type_path, false) ->
      Some (module_expr.mod_type, module_type_path)
    | _ -> None in
  of_module_expr name functor_parameters as_expression None module_expr

and of_module_expr
  (name : Name.t)
  (functor_parameters : functor_parameters)
  (as_expression : (Types.module_type * Path.t) option)
  (module_type_annotation : Typedtree.module_type option)
  (module_expr : module_expr)
  : t Monad.t =
  let* module_typ =
    match module_type_annotation with
    | Some module_typ ->
      let* module_typ = ModuleTyp.of_ocaml module_typ in
      let functor_parameter_names =
        snd functor_parameters |>
        List.map (fun (name, _) -> name) in
      let* (_, module_typ) =
        ModuleTyp.to_typ
          functor_parameter_names (Name.to_string name) true module_typ in
      return (Some module_typ)
    | None -> return None in
  match module_expr.mod_desc with
  | Tmod_structure structure ->
    let* structure = of_structure structure in
    let* e =
      match as_expression with
      | Some (module_type, module_type_path) ->
        let typ_vars = Name.Map.empty in
        let* module_typ_params_arity =
          ModuleTypParams.get_module_typ_typ_params_arity module_type in
        let* values = Exp.ModuleTypValues.get typ_vars module_type in
        let mixed_path_of_value_or_typ (name : Name.t) : MixedPath.t Monad.t =
          return (MixedPath.of_name name) in
        let* e =
          Exp.build_module
            module_typ_params_arity
            values
            module_type_path
            mixed_path_of_value_or_typ in
        return (Some (e, module_typ))
      | None -> return None in
    return (Module (name, functor_parameters, structure, e))
  | Tmod_ident (path, _) ->
    begin match as_expression with
    | Some (module_type, _) ->
      let* module_exp =
        Exp.of_module_expr Name.Map.empty module_expr (Some module_type) in
      return (ModuleExpression (name, module_typ, module_exp))
    | None ->
      let* reference = PathName.of_path_with_convert false path in
      return (ModuleSynonym (name, reference))
    end
  | Tmod_apply _ ->
      let* module_exp = Exp.of_module_expr Name.Map.empty module_expr None in
      return (ModuleExpression (name, module_typ, module_exp))
  | Tmod_functor (parameter, module_expr) ->
    let* functor_parameters =
      match parameter with
      | Unit -> return functor_parameters
      | Named (ident, _, module_type_arg) ->
        let* x = Name.of_optional_ident false ident in
        let* module_type_arg = ModuleTyp.of_ocaml module_type_arg in
        let id = Name.string_of_optional_ident ident in
        let* ((_, _, free_vars_arg), typ_arg) =
          ModuleTyp.to_typ [] id false module_type_arg in
        let (free_vars_params, params) = functor_parameters in
        return (
          free_vars_params @ free_vars_arg,
          params @ [(x, typ_arg)]
        ) in
    of_module name functor_parameters module_expr false
  | Tmod_constraint (module_expr, _, annotation, _) ->
    let module_type_annotation =
      match annotation with
      | Tmodtype_explicit module_type -> Some module_type
      | Tmodtype_implicit -> module_type_annotation in
    of_module_expr
      name functor_parameters as_expression module_type_annotation module_expr
  | Tmod_unpack _ ->
    return (Error
      "Cannot unpack first-class modules at top-level due to a universe inconsistency"
    )

(** Pretty-print a structure to Coq. *)
let rec to_coq (fargs : int option) (defs : t list) : SmartPrint.t =
  let with_args =
    match fargs with
    | None -> false
    | Some _ -> true in
  let rec to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.to_coq with_args value
    | AbstractValue (name, typ_vars, typ) ->
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
        !^ "forall" ^^ nest (parens (typ_vars ^^ !^ ":" ^^ Pp.set)) ^-^ !^ ","
      ) ^^
      Type.to_coq None None typ ^-^ !^ "."
    | TypeDefinition typ_def -> TypeDefinition.to_coq with_args typ_def
    | Module (name, (free_vars_params, params), defs, e) ->
      let is_functor =
        match params with
        | [] -> false
        | _ :: _ -> true in
      let fargs_instance =
        nest (
          Name.to_coq name ^-^ !^ "." ^-^ !^ "Build_FArgs" ^^
          separate space (params |> List.map (
            fun (name, _) -> Name.to_coq name
          ))
        ) in
      let nb_new_fargs_typ_params = List.length free_vars_params in
      let nb_fargs_typ_params =
        match fargs with
        | None -> nb_new_fargs_typ_params
        | Some fargs -> 1 + fargs + nb_new_fargs_typ_params in
      let fargs =
        match fargs with
        | None ->
          if is_functor then
            Some nb_new_fargs_typ_params
          else
            None
        | Some fargs -> Some (fargs + nb_new_fargs_typ_params) in
      let final_item_name =
        if is_functor then !^ "functor" else !^ "module" in
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^
        newline ^^
        indent (
          begin if is_functor then
            nest (
              !^ "Class" ^^ !^ "FArgs" ^^ Pp.args with_args ^^
              ModuleTyp.to_coq_grouped_free_vars free_vars_params ^^
              !^ ":=" ^^
              !^ "{" ^^ newline ^^
              indent (
                separate empty (params |> List.map (
                fun (name, typ) ->
                  nest (
                    Name.to_coq name ^^ !^ ":" ^^ Type.to_coq None None typ ^-^
                    !^ ";" ^^ newline
                  )
                ))
              )
              ^^ !^ "}" ^-^ !^ "." ^^ newline ^^
              begin if nb_fargs_typ_params = 0 then
                empty
              else
                !^ "Arguments" ^^ !^ "Build_FArgs" ^^
                braces (nest (separate space (
                  Pp.n_underscores nb_fargs_typ_params
                ))) ^-^ !^ "." ^^ newline
              end ^^
              newline
            )
          else
            empty
          end ^^
          to_coq fargs defs ^^
          begin match e with
          | Some (e, typ_annotation) ->
            newline ^^ newline ^^
            nest (
              !^ "Definition" ^^ final_item_name ^^
              begin if is_functor then
                !^ "`{FArgs}"
              else
                Pp.args with_args
              end ^^
              !^ ":=" ^^ Exp.to_coq false e ^-^ !^ "."
            )
          | None -> empty
          end
        ) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ "." ^^
        begin match e with
        | Some (_, typ_annotation) ->
          newline ^^
          nest (
            !^ "Definition" ^^ Name.to_coq name ^^ Pp.args with_args ^^
            ModuleTyp.to_coq_functor_parameters_modules free_vars_params params ^^
            begin match typ_annotation with
            | Some typ_annotation ->
              !^ ": " ^-^ Type.to_coq None None typ_annotation
            | _ -> empty
            end ^^ !^ ":=" ^^
            nest (
              begin if is_functor then
                nest (
                  !^ "let" ^^ !^ "'_" ^^ !^ ":=" ^^ fargs_instance ^^ !^ "in"
                ) ^^
                newline
              else
                empty
              end ^^
              Name.to_coq name ^-^ !^ "." ^-^ final_item_name ^-^ !^ "."
            )
          )
        | None -> empty
        end
      )
    | ModuleExpression (name, typ, e) ->
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^ Pp.args with_args ^^
        begin match typ with
        | None -> empty
        | Some typ -> !^ ":" ^^ Type.to_coq None None typ
        end ^^ !^ ":=" ^^
        Exp.to_coq false e ^-^ !^ "."
      )
    | ModuleInclude reference ->
      nest (!^ "Include" ^^ PathName.to_coq reference ^-^ !^ ".")
    | ModuleIncludeItem (name, typ_vars, mixed_path) ->
      nest (
        !^ "Definition" ^^ Name.to_coq name ^^ Pp.args with_args ^^
        Name.to_coq_list_or_empty typ_vars (fun typ_vars ->
          nest (braces (typ_vars ^^ !^ ":" ^^ Pp.set))
        ) ^^
        !^ ":=" ^^
        nest (separate space (
          MixedPath.to_coq mixed_path ::
          (typ_vars |> List.map (fun typ_var ->
            nest (parens (
              Name.to_coq typ_var ^^ !^ ":=" ^^ Name.to_coq typ_var
            ))
          ))
        )) ^-^
        !^ "."
      )
    | ModuleSynonym (name, reference) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^^ !^ ":=" ^^ PathName.to_coq reference ^-^ !^ "."
      )
    | Signature (name, signature) -> Signature.to_coq_definition name signature
    | Documentation (message, defs) ->
      nest (
        !^ ( "(** " ^ message ^ " *)") ^^ newline ^^
        to_coq fargs defs
      )
    | Error message -> !^ ( "(* " ^ message ^ " *)")
    | ErrorMessage (message, def) ->
      nest (
        Error.to_comment message ^^ newline ^^
        to_coq_one def
      ) in
  separate (newline ^^ newline) (defs |> List.map to_coq_one)
