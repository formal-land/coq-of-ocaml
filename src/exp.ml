(** An expression. *)
open Typedtree
open SmartPrint
open Monad.Notations

module Header = struct
  type t = {
    name : Name.t;
    typ_vars : Name.t list;
    args : (Name.t * Type.t) list;
    typ : Type.t option }
end

module Definition = struct
  type 'a t = {
    is_rec : Recursivity.t;
    cases : (Header.t * 'a) list }
end

type match_existential_cast = {
  new_typ_vars : Name.t list;
  bound_vars : (Name.t * Type.t) list;
  return_typ : Type.t;
  cast_with_axioms : bool }

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type t =
  | Constant of Constant.t
  | Variable of MixedPath.t * string list
  | Tuple of t list (** A tuple of expressions. *)
  | Constructor of PathName.t * string list * t list
    (** A constructor name, some implicits and a list of arguments. *)
  | Apply of t * t list (** An application. *)
  | Function of Name.t * t (** An argument name and a body. *)
  | LetVar of Name.t * t * t
  | LetFun of t option Definition.t * t
  | LetTyp of Name.t * Name.t list * Type.t * t
    (** The definition of a type. It is used to represent module values. *)
  | Match of t * (Pattern.t * match_existential_cast option * t) list * t option
    (** Match an expression to a list of patterns. *)
  | Record of (PathName.t * t) list
    (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t (** Access to a field of a record. *)
  | IfThenElse of t * t * t (** The "else" part may be unit. *)
  | Module of int * (PathName.t * int * t) list
    (** The value of a first-class module. *)
  | ModuleNested of (string option * PathName.t * t) list
    (** The value of a first-class module inside another module
        (no existentials). There may be error messages. *)
  | Functor of Name.t * Type.t * t
    (** A functor. *)
  | TypeAnnotation of t * Type.t
    (** Annotate with a type. *)
  | Error of string (** An error message for unhandled expressions. *)
  | ErrorArray of t list (** An error produced by an array of elements. *)
  | ErrorTyp of Type.t (** An error composed of a type. *)
  | ErrorMessage of t * string (** An expression together with an error message. *)

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

let error_message (e : t) (category : Error.Category.t) (message : string) : t Monad.t =
  raise (ErrorMessage (e, message)) category message

let error_message_in_module
  (field : Name.t option)
  (e : t)
  (category : Error.Category.t)
  (message : string)
  : (string option * Name.t option * t) option Monad.t =
  raise (Some (Some message, field, e)) category message

let get_module_typ_values
  (typ_vars : Name.t Name.Map.t)
  (module_typ : Types.module_type)
  : (Name.t * int) list Monad.t =
  get_env >>= fun env ->
  match Mtype.scrape env module_typ with
  | Mty_signature signature ->
    signature |> Monad.List.filter_map (fun item ->
      match item with
      | Types.Sig_value (ident, { val_type; _ }) ->
        Type.of_typ_expr true typ_vars val_type >>= fun (_, _, new_typ_vars) ->
        return (Some (Name.of_ident true ident, Name.Set.cardinal new_typ_vars))
      | _ -> return None
    )
  | _ -> return []

let rec any_patterns_with_ith_true (is_guarded : bool) (i : int) (n : int)
  : Pattern.t list =
  if n = 0 then
    []
  else
    let head =
      if i = 0 && is_guarded then
        Pattern.Constructor (PathName.true_value, [])
      else
        Pattern.Any in
    head :: any_patterns_with_ith_true is_guarded (i - 1) (n - 1)

(** Import an OCaml expression. *)
let rec of_expression (typ_vars : Name.t Name.Map.t) (e : expression)
  : t Monad.t =
  Attribute.of_attributes e.exp_attributes >>= fun attributes ->
  set_env e.exp_env (
  set_loc (Loc.of_location e.exp_loc) (
  match e.exp_desc with
  | Texp_ident (path, loc, _) ->
    let implicits = Attribute.get_implicits attributes in
    MixedPath.of_path true path (Some loc.txt) >>= fun x ->
    return (Variable (x, implicits))
  | Texp_constant constant ->
    Constant.of_constant constant >>= fun constant ->
    return (Constant constant)
  | Texp_let (is_rec, cases, e2) ->
    of_expression typ_vars e2 >>= fun e2 ->
    of_let typ_vars is_rec cases e2
  | Texp_function {
      cases = [{
        c_lhs = {pat_desc = Tpat_var (x, _); _};
        c_rhs = e;
        _
      }];
      _
    }
  | Texp_function {
      cases = [{
        c_lhs = { pat_desc = Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _); _ };
        c_rhs = e;
        _
      }];
      _
    } ->
    let x = Name.of_ident true x in
    of_expression typ_vars e >>= fun e ->
    return (Function (x, e))
  | Texp_function { cases; _ } ->
    let is_gadt_match = Attribute.have_match_gadt attributes in
    open_cases typ_vars cases is_gadt_match >>= fun (x, e) ->
    return (Function (x, e))
  | Texp_apply (e_f, e_xs) ->
    of_expression typ_vars e_f >>= fun e_f ->
    (e_xs |> Monad.List.map (fun (_, e_x) ->
      match e_x with
      | Some e_x -> of_expression typ_vars e_x
      | None ->
        error_message
          (Error "expected_argument")
          Unexpected
          "expected an argument"
    )) >>= fun e_xs ->
    return (Apply (e_f, e_xs))
  | Texp_match (e, cases, exception_cases, _) ->
    let is_gadt_match = Attribute.have_match_gadt attributes in
    of_expression typ_vars e >>= fun e ->
    of_match typ_vars e cases exception_cases is_gadt_match
  | Texp_tuple es ->
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    return (Tuple es)
  | Texp_construct (_, constructor_description, es) ->
    let implicits = Attribute.get_implicits attributes in
    begin match constructor_description.cstr_tag with
    | Cstr_extension _ ->
      raise
        (Variable (
          MixedPath.of_name (Name.of_string true "extensible_type_value"),
          []
        ))
        NotSupported
        "Values of extensible types are not handled"
    | _ ->
      let x = PathName.of_constructor_description constructor_description in
      Monad.List.map (of_expression typ_vars) es >>= fun es ->
      return (Constructor (x, implicits, es))
    end
  | Texp_variant (label, e) ->
    PathName.constructor_of_variant label >>= fun path_name ->
    let constructor =
      Variable (MixedPath.PathName path_name, []) in
    begin match e with
    | None -> return constructor
    | Some e ->
      of_expression typ_vars e >>= fun e ->
      return (Apply (constructor, [e]))
    end
  | Texp_record { fields; extended_expression; _ } ->
      Array.to_list fields |> Monad.List.filter_map (
        fun (label_description, definition) ->
          let x_e =
            match definition with
            | Kept _ -> None
            | Overridden (_, e) ->
              let x = PathName.of_label_description label_description in
              Some (x, e) in
          match x_e with
          | None -> return None
          | Some (x, e) ->
            of_expression typ_vars e >>= fun e ->
            return (Some (x, e))
      ) >>= fun fields ->
      begin match extended_expression with
      | None -> return (Record fields)
      | Some extended_expression ->
        of_expression typ_vars extended_expression >>= fun extended_e ->
        return (
          List.fold_left
            (fun extended_e (x, e) ->
              Apply (
                Variable (MixedPath.PathName (PathName.prefix_by_with x), []),
                [e; extended_e]
              )
            )
            extended_e
            fields
        )
    end
  | Texp_field (e, _, label_description) ->
    let x = PathName.of_label_description label_description in
    of_expression typ_vars e >>= fun e ->
    return (Field (e, x))
  | Texp_ifthenelse (e1, e2, e3) ->
    of_expression typ_vars e1 >>= fun e1 ->
    of_expression typ_vars e2 >>= fun e2 ->
    (match e3 with
    | None -> return (Tuple [])
    | Some e3 -> of_expression typ_vars e3) >>= fun e3 ->
    return (IfThenElse (e1, e2, e3))
  | Texp_sequence (e1, e2) ->
    of_expression typ_vars e2 >>= fun e2 ->
    set_loc (Loc.of_location e1.exp_loc) (
    error_message
      (ErrorMessage (e2, "instruction_sequence \";\""))
      SideEffect
      (
        "Sequences of instructions are ignored (operator \";\")\n\n" ^
        "Alternative: use a monad to sequence side-effects."
      )
    )
  | Texp_try (e, _) ->
    of_expression typ_vars e >>= fun e ->
    error_message
      (Apply (Error "try", [e]))
      SideEffect
      (
        "Try-with are not handled\n\n" ^
        "Alternative: use sum types (\"option\", \"result\", ...) to represent an error case."
      )
  | Texp_setfield (e_record, _, { lbl_name; _ }, e) ->
    of_expression typ_vars e_record >>= fun e_record ->
    of_expression typ_vars e >>= fun e ->
    error_message
      (Apply (
        Error "set_record_field",
        [e_record; Constant (Constant.String lbl_name); e]
      ))
      SideEffect
      "Set record field not handled."
  | Texp_array es ->
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    error_message (ErrorArray es) NotSupported "Arrays not handled."
  | Texp_while _ ->
    error_message (Error "while") SideEffect "While loops not handled."
  | Texp_for _ ->
    error_message (Error "for") SideEffect "For loops not handled."
  | Texp_send _ ->
    error_message
      (Error "send")
      NotSupported
      "Sending method message is not handled"
  | Texp_new _ ->
    error_message
      (Error "new")
      NotSupported
      "Creation of new objects is not handled"
  | Texp_instvar _ ->
    error_message
      (Error "instance_variable")
      NotSupported
      "Creating an instance variable is not handled"
  | Texp_setinstvar _ ->
    error_message
      (Error "set_instance_variable")
      SideEffect
      "Setting an instance variable is not handled"
  | Texp_override _ ->
    error_message (Error "override") NotSupported "Overriding is not handled"
  | Texp_letmodule (x, _, module_expr, e) ->
    let x = Name.of_ident true x in
    of_module_expr typ_vars module_expr None >>= fun value ->
    of_expression typ_vars e >>= fun e ->
    return (LetVar (x, value, e))
  | Texp_letexception _ ->
    error_message
      (Error "let_exception")
      SideEffect
      "Let of exception is not handled"
  | Texp_assert e ->
    of_expression typ_vars e >>= fun e ->
    error_message
      (Apply (Error "assert", [e]))
      SideEffect
      "Assert instruction is not handled."
  | Texp_lazy e ->
    of_expression typ_vars e >>= fun e ->
    error_message
      (Apply (Error "lazy", [e]))
      SideEffect
      "Lazy expressions are not handled"
  | Texp_object _ ->
    error_message
      (Error "object")
      NotSupported
      "Creation of objects is not handled"
  | Texp_pack module_expr -> of_module_expr typ_vars module_expr None
  | Texp_unreachable ->
    error_message
      (Error "unreachable")
      NotSupported
      "Unreachable expressions are not supported"
  | Texp_extension_constructor _ ->
    error_message
      (Error "extension")
      NotSupported
      "Construction of extensions is not handled"))

and of_match
  (typ_vars : Name.t Name.Map.t)
  (e : t)
  (cases : case list)
  (exception_cases : case list)
  (is_gadt_match : bool)
  : t Monad.t =
  (cases |> Monad.List.filter_map (fun {c_lhs; c_guard; c_rhs} ->
    set_loc (Loc.of_location c_lhs.pat_loc) (
    let bound_vars =
      Typedtree.pat_bound_idents c_lhs |> List.rev |> List.map
        (fun ident ->
          let { Types.val_type; _ } =
            Env.find_value (Path.Pident ident) c_rhs.exp_env in
          let name = Name.of_ident true ident in
          (name, val_type)
        ) in
    Type.existential_typs_of_typs (List.map snd bound_vars) >>= fun existentials ->
    Monad.List.map
      (fun (name, typ) ->
        Type.of_typ_expr true typ_vars typ >>= fun (typ, _, _) ->
        return (name, typ)
      )
      bound_vars >>= fun bound_vars ->
    Type.of_typ_expr true typ_vars c_rhs.exp_type >>= fun (typ, _, _) ->
    let existential_cast =
      Some {
        new_typ_vars = Name.Set.elements existentials;
        bound_vars;
        return_typ = typ;
        cast_with_axioms = is_gadt_match;
      } in
    begin match c_guard with
    | Some guard ->
      of_expression typ_vars guard >>= fun guard ->
      return (Some guard)
    | None -> return None
    end >>= fun guard ->
    Pattern.of_pattern c_lhs >>= fun pattern ->
    of_expression typ_vars c_rhs >>= fun e ->
    return (
      Util.Option.map pattern (fun pattern ->
      (pattern, existential_cast, guard, e))
    ))
  )) >>= fun cases_with_guards ->
  let guards =
    cases_with_guards |> Util.List.filter_map (function
      | (p, _, Some guard, _) -> Some (p, guard)
      | _ -> None
    ) in
  let guard_checks =
    guards |> List.map (fun (p, guard) ->
      Match (
        e,
        [
          (p, None, guard);
          (
            Pattern.Any,
            None,
            Variable (MixedPath.PathName PathName.false_value, [])
          )
        ],
        None
      )
    ) in
  let e =
    match guards with
    | [] -> e
    | _ :: _ -> Tuple (e :: guard_checks) in
  let i = ref (-1) in
  let nb_guards = List.length guard_checks in
  let cases =
    cases_with_guards |> List.map (fun (p, existential_cast, guard, rhs) ->
      let is_guarded = match guard with Some _ -> true | None -> false in
      begin if is_guarded then
        i := !i + 1
      end;
      let p =
        if nb_guards = 0 then
          p
        else
          Pattern.Tuple (
            p :: any_patterns_with_ith_true is_guarded !i nb_guards
          ) in
      (p, existential_cast, rhs)
    ) in
  (exception_cases |> Monad.List.filter_map (fun {c_lhs; c_guard; c_rhs} ->
    set_loc (Loc.of_location c_lhs.pat_loc) (
    match c_guard with
    | Some guard_exp ->
      of_expression typ_vars guard_exp >>= fun guard_exp ->
      begin match guard_exp with
      | Constructor ({ PathName.path = []; base = Name.Make "false" }, _, []) ->
        of_expression typ_vars c_rhs >>= fun c_rhs ->
        return (Some c_rhs)
      | _ ->
        raise
          None
          Unexpected
          "Expected `false` as guard on the exception case to represent the default GADT case"
      end
    | None ->
      raise None NotSupported (
        "Pattern-matching on exceptions not supported\n\n" ^
        "Only the special case `| exception _ when false -> ...` is supported for default value of GADT pattern-matching"
      )
    )
  )) >>= fun default_values ->
  let default_value =
    match default_values with
    | [default_value] -> Some default_value
    | _ -> None in
  return (Match (e, cases, default_value))

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases
  (typ_vars : Name.t Name.Map.t)
  (cases : case list)
  (is_gadt_match : bool)
  : (Name.t * t) Monad.t =
  let name = Name.of_string false "function_parameter" in
  let e = Variable (MixedPath.of_name name, []) in
  of_match typ_vars e cases [] is_gadt_match >>= fun e ->
  return (name, e)

and import_let_fun
  (typ_vars : Name.t Name.Map.t)
  (at_top_level : bool)
  (is_rec : Asttypes.rec_flag)
  (cases : value_binding list)
  : t option Definition.t Monad.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  (cases |> Monad.List.filter_map (fun { vb_pat = p; vb_expr; vb_attributes; _ } ->
    Attribute.of_attributes vb_attributes >>= fun attributes ->
    let is_axiom = Attribute.have_axiom attributes in
    set_env vb_expr.exp_env (
    set_loc (Loc.of_location p.pat_loc) (
    Pattern.of_pattern p >>= fun p ->
    (match p with
    | Some Pattern.Any -> return None
    | Some (Pattern.Variable x) -> return (Some x)
    | _ ->
      raise None Unexpected "A variable name instead of a pattern was expected."
    ) >>= fun x ->
    Type.of_typ_expr true typ_vars vb_expr.exp_type >>= fun (e_typ, typ_vars, new_typ_vars) ->
    match x with
    | None -> return None
    | Some x ->
      of_expression typ_vars vb_expr >>= fun e ->
      let (args_names, e_body) = open_function e in
      let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
      let header = {
        Header.name = x;
        typ_vars = Name.Set.elements new_typ_vars;
        args = List.combine args_names args_typs;
        typ = Some e_body_typ
      } in
      let e_body = if is_axiom then None else Some e_body in
      return (Some (header, e_body))
    )
  ))) >>= fun cases ->
  let result = { Definition.is_rec = is_rec; cases } in
  match (at_top_level, result) with
  | (false, { is_rec = Recursivity.New true; cases = _ :: _ :: _ }) ->
    raise
      result
      NotSupported
      "Mutually recursive definition are only handled at top-level"
  | _ -> return result

and of_let
  (typ_vars : Name.t Name.Map.t)
  (is_rec : Asttypes.rec_flag)
  (cases : Typedtree.value_binding list)
  (e2 : t)
  : t Monad.t =
  match cases with
  | [{
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
     }] when PathName.is_unit (PathName.of_path_without_convert false path) ->
     raise
      (ErrorMessage (e2, "top_level_evaluation"))
      SideEffect
      "Top-level evaluations are not handled"
  | [{ vb_pat = p; vb_expr = e1; _ }] when
    begin match e1.exp_desc with
    | Texp_function _ -> false
    | _ -> true
    end ->
    Pattern.of_pattern p >>= fun p ->
    of_expression typ_vars e1 >>= fun e1 ->
    begin match p with
    | Some (Pattern.Variable x) -> return (LetVar (x, e1, e2))
    | Some p -> return (Match (e1, [p, None, e2], None))
    | None -> return (Match (e1, [], None))
    end
  | _ ->
    import_let_fun typ_vars false is_rec cases >>= fun def ->
    return (LetFun (def, e2))

and of_module_expr
  (typ_vars : Name.t Name.Map.t)
  (module_expr : Typedtree.module_expr)
  (module_type : Types.module_type option)
  : t Monad.t =
  let { mod_desc; mod_env; mod_loc; mod_type = local_module_type; _ } = module_expr in
  set_env mod_env (
  set_loc (Loc.of_location mod_loc) (
  match mod_desc with
  | Tmod_ident (path, loc) ->
    let default_result =
      MixedPath.of_path true path (Some loc.txt) >>= fun path ->
      return (Variable (path, [])) in
    IsFirstClassModule.is_module_typ_first_class local_module_type >>= fun is_first_class ->
    let local_module_type_path =
      match is_first_class with
      | Found local_module_type_path -> Some local_module_type_path
      | Not_found _ -> None in
      begin match module_type with
      | None -> default_result
      | Some module_type ->
        IsFirstClassModule.is_module_typ_first_class
          module_type >>= fun is_first_class ->
        begin match is_first_class with
        | Found module_type_path ->
          ModuleTypParams.get_module_typ_nb_of_existential_variables
            module_type >>= fun nb_of_existential_variables ->
          get_module_typ_values typ_vars module_type >>= fun values ->
          let fields =
            values |> List.map (fun (value, nb_free_vars) ->
              (
                PathName.of_path_and_name_with_convert module_type_path value,
                nb_free_vars,
                Variable (
                  begin match local_module_type_path with
                  | Some local_module_type_path ->
                    MixedPath.Access (
                      MixedPath.PathName
                        (PathName.of_path_with_convert false path),
                      PathName.of_path_and_name_with_convert
                        local_module_type_path
                        value,
                      false
                    )
                  | None ->
                    MixedPath.PathName (
                      PathName.of_path_and_name_with_convert path value
                    )
                  end,
                  []
                )
              )
            ) in
          return (Module (nb_of_existential_variables, fields))
        | Not_found _ -> default_result
        end
      end
  | Tmod_structure structure ->
    let module_type =
      match module_type with
      | Some module_type -> module_type
      | None -> local_module_type in
    IsFirstClassModule.is_module_typ_first_class
      module_type >>= fun is_first_class ->
    begin match is_first_class with
    | IsFirstClassModule.Found signature_path ->
      of_structure typ_vars signature_path module_type structure.str_items
    | IsFirstClassModule.Not_found reason ->
      error_message
        (Error "first_class_module_value_of_unknown_signature")
        FirstClassModule
        (
          "The signature name of this module could not be found\n\n" ^
          reason
        )
    end
  | Tmod_functor (ident, _, module_type_arg, e) ->
    begin match module_type_arg with
    | None ->
      error_message
        (Error "functor_without_argument_annotation")
        NotSupported
        "Expected an annotation to get the module type of the parameter of this functor"
    | Some module_type_arg ->
      let x = Name.of_ident false ident in
      ModuleTyp.of_ocaml module_type_arg >>= fun module_type_arg ->
      of_module_expr typ_vars e None >>= fun e ->
      return (Functor (x, ModuleTyp.to_typ module_type_arg, e))
    end
  | Tmod_apply (e1, e2, _) ->
    let expected_module_type_for_e2 =
      match e1.mod_type with
      | Mty_functor (_, mod_typ_arg, _) -> mod_typ_arg
      | _ -> None in
    of_module_expr typ_vars e1 None >>= fun e1 ->
    of_module_expr typ_vars e2 expected_module_type_for_e2 >>= fun e2 ->
    return (Apply (e1, [e2]))
  | Tmod_constraint (module_expr, mod_type, annotation, _) ->
    let module_type =
      match module_type with
      | Some _ -> module_type
      | None -> Some mod_type in
    of_module_expr typ_vars module_expr module_type >>= fun e ->
    begin match annotation with
    | Tmodtype_implicit -> return e
    | Tmodtype_explicit module_type ->
      ModuleTyp.of_ocaml module_type >>= fun module_type ->
      return (TypeAnnotation (e, ModuleTyp.to_typ module_type))
    end
  | Tmod_unpack (e, _) -> of_expression typ_vars e
  ))

and of_structure
  (typ_vars : Name.t Name.Map.t)
  (signature_path : Path.t)
  (module_type : Types.module_type)
  (items : Typedtree.structure_item list)
  : t Monad.t =
  ModuleTypParams.get_module_typ_nb_of_existential_variables
    module_type >>= fun nb_of_existential_variables ->
  get_module_typ_values typ_vars module_type >>= fun values ->
  let fields =
    values |> List.map (fun (value, nb_free_vars) ->
      (
        PathName.of_path_and_name_with_convert signature_path value,
        nb_free_vars,
        Variable (MixedPath.of_name value, [])
      )
    ) in
  let e_next = Module (nb_of_existential_variables, fields) in
  Monad.List.fold_right
    (fun item e_next ->
      set_env item.str_env (
      set_loc (Loc.of_location item.str_loc) (
      match item.str_desc with
      | Tstr_eval _ ->
        raise
          (ErrorMessage (e_next, "top_level_evaluation"))
          SideEffect
          "Top-level evaluation is not handled"
      | Tstr_value (rec_flag, cases) -> of_let typ_vars rec_flag cases e_next
      | Tstr_primitive _ ->
        raise
          (ErrorMessage (e_next, "primitive"))
          NotSupported
          "Primitive not handled"
      | Tstr_type (_, typs) ->
        begin match typs with
        | [typ] ->
          begin match typ with
          | {
              typ_id;
              typ_type = {
                type_kind = Type_abstract;
                type_manifest = Some typ;
                type_params;
                _
              };
              _
            } ->
            let name = Name.of_ident false typ_id in
            (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
            Type.of_type_expr_without_free_vars typ >>= fun typ ->
            return (LetTyp (name, typ_args, typ, e_next))
          | _ ->
            raise
              (ErrorMessage (e_next, "typ_definition"))
              NotSupported
              "Only type synonyms are handled here"
          end
        | _ ->
          raise
            (ErrorMessage (e_next, "mutual_typ_definition"))
            NotSupported
            "Mutually recursive type definition not handled here"
        end
      | Tstr_typext _ ->
        raise
          (ErrorMessage (e_next, "type_extension"))
          NotSupported
          "Type extension not handled"
      | Tstr_exception _ ->
        raise
          (ErrorMessage (e_next, "exception"))
          SideEffect
          "Exception not handled"
      | Tstr_module { mb_id; mb_expr; _ } ->
        let name = Name.of_ident false mb_id in
        of_module_expr typ_vars mb_expr None >>= fun value ->
        return (LetVar (name, value, e_next))
      | Tstr_recmodule _ ->
        raise
          (ErrorMessage (e_next, "recursive_module"))
          NotSupported
          "Recursive modules not handled"
      | Tstr_modtype _ ->
        raise
          (ErrorMessage (e_next, "module_type"))
          NotSupported
          "Module type not handled in module with a named signature"
      | Tstr_open _ ->
        raise
          (ErrorMessage (e_next, "open"))
          NotSupported
          "Open not handled in module with a named signature"
      | Tstr_class _ ->
        raise
          (ErrorMessage (e_next, "class"))
          NotSupported
          "Class not handled"
      | Tstr_class_type _ ->
        raise
          (ErrorMessage (e_next, "class_type"))
          NotSupported
          "Class type not handled"
      | Tstr_include { incl_mod; incl_type; _ } ->
        begin match incl_mod.mod_desc with
        | Tmod_ident (path, _)
        | Tmod_constraint ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
          let incl_module_type = Types.Mty_signature incl_type in
          IsFirstClassModule.is_module_typ_first_class
            incl_module_type >>= fun is_first_class ->
          begin match is_first_class with
          | Found incl_signature_path ->
            let path_name = PathName.of_path_with_convert false path in
            of_include path_name incl_signature_path incl_type e_next
          | Not_found reason ->
            raise
              (ErrorMessage (e_next, "include_without_named_signature"))
              NotSupported
              (
                "We did not find a signature name for the include of this module\n\n" ^
                reason
              )
          end
        | _ ->
          raise
            (ErrorMessage (e_next, "unhandled_include"))
            NotSupported
            "The include of this kind of module is not supported"
        end
      | Tstr_attribute _ -> return e_next))
    )
    items
    e_next

and of_include
  (module_path_name : PathName.t)
  (signature_path : Path.t)
  (signature : Types.signature)
  (e_next : t)
  : t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature ->
    of_include module_path_name signature_path signature e_next >>= fun e_next ->
    begin match signature_item with
    | Sig_value (ident, _) | Sig_type (ident, _, _) ->
      let is_value =
        match signature_item with Sig_value _ -> true | _ -> false in
      let name = Name.of_ident is_value ident in
      return (
        LetVar (
          name,
          Variable (
            MixedPath.Access (
              MixedPath.PathName module_path_name,
              PathName.of_path_and_name_with_convert
                signature_path
                name,
              false
            ),
            []
          ),
          e_next
        )
      )
    | Sig_typext _ | Sig_module _ | Sig_modtype _ | Sig_class _
      | Sig_class_type _ -> return e_next
    end

let rec to_coq_n_underscores (n : int) : SmartPrint.t list =
  if n = 0 then
    []
  else
    (!^ "_") :: to_coq_n_underscores (n - 1)

let rec flatten_list (e : t) : t list option =
  match e with
  | Constructor (x, _, es) ->
    begin match (x, es) with
    | ({ PathName.path = []; base = Name.Make "[]" }, []) -> Some []
    | ({ PathName.path = []; base = Name.Make "cons" }, [e; es]) ->
      begin match flatten_list es with
      | Some es -> Some (e :: es)
      | None -> None
      end
    | _ -> None
    end
  | _ -> None

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq c
  | Variable (x, implicits) ->
    let x = MixedPath.to_coq x in
    begin match implicits with
    | [] -> x
    | _ :: _ ->
      parens (separate space (
        x :: List.map (fun implicit -> !^ implicit) implicits)
      )
    end
  | Tuple es ->
    if es = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (x, implicits, es) ->
    begin match flatten_list e with
    | Some [] -> !^ "[]"
    | Some es -> OCaml.list (to_coq false) es
    | None ->
      let arguments =
        List.map (fun implicit -> !^ implicit) implicits @
        List.map (to_coq true) es in
      begin match arguments with
      | [] -> PathName.to_coq x
      | _ :: _ ->
        Pp.parens paren @@ nest @@
          separate space (PathName.to_coq x :: arguments)
      end
    end
  | Apply (e_f, e_xs) ->
    Pp.parens paren @@ nest @@ (separate space (
      List.map (to_coq true) (e_f :: e_xs)
    ))
  | Function (x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | LetVar (x, e1, e2) ->
    begin match e1 with
    | Variable (PathName { path = []; base }, []) when Name.equal base x ->
      to_coq paren e2
    | _ ->
      Pp.parens paren @@ nest (
        !^ "let" ^^ Name.to_coq x ^-^ !^ " :=" ^^ to_coq false e1 ^^ !^ "in" ^^
        newline ^^ to_coq false e2
      )
    end
  | LetFun (def, e) ->
    (* There should be only on case for recursive definitionss. *)
    Pp.parens paren @@ nest (separate newline
      (def.Definition.cases |> List.mapi (fun index (header, e) ->
        let first_case = index = 0 in
        (if first_case then (
          !^ "let" ^^
          (if Recursivity.to_bool def.Definition.is_rec then !^ "fix" else empty)
        ) else
          !^ "with") ^^
        Name.to_coq header.Header.name ^^
        (if header.Header.typ_vars = []
        then empty
        else braces @@ group (
          separate space (List.map Name.to_coq header.Header.typ_vars) ^^
          !^ ":" ^^ Pp.set)) ^^
        group (separate space (header.Header.args |> List.map (fun (x, x_typ) ->
          parens (nest (
            Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None x_typ
          )))
        )) ^^
        (if Recursivity.to_bool def.Definition.is_rec then
          match header.Header.args with
          | [] -> empty
          | (x, _) :: _ -> braces (nest (!^ "struct" ^^ Name.to_coq x))
        else
          empty
        ) ^^
        (match header.Header.typ with
        | None -> empty
        | Some typ -> !^ ": " ^-^ Type.to_coq None None typ) ^-^
        !^ " :=" ^^ newline ^^
        indent (
          match e with
          | None -> !^ "axiom"
          | Some e -> to_coq false e
        )
      )) ^^ !^ "in" ^^ newline ^^ to_coq false e)
  | LetTyp (x, typ_args, typ, e) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^^
      begin match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set)
      end ^^ !^ ":=" ^^ Type.to_coq None None typ ^^ !^ "in" ^^
      newline ^^ to_coq false e
    )
  | Match (e, cases, default_value) ->
    begin match (cases, default_value) with
    | ([(pattern, existential_cast, e2)], None) ->
      Pp.parens paren @@ nest (
        !^ "let" ^^ !^ "'" ^-^ Pattern.to_coq false pattern ^-^ !^ " :=" ^^
        to_coq false e ^^ !^ "in" ^^ newline ^^
        cast_existentials existential_cast e2
      )
    | _ ->
      nest (
        !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
        separate space (cases |> List.map (fun (p, existential_cast, e) ->
          nest (
            !^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^
            cast_existentials existential_cast e ^^ newline
          )
        )) ^^
        (match default_value with
        | None -> empty
        | Some default_value ->
          nest (
            !^ "|" ^^ !^ "_" ^^ !^ "=>" ^^ to_coq false default_value ^^ newline
          )
        ) ^^
        !^ "end"
      )
    end
  | Record fields ->
    nest (
      !^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
        nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e)
      )) ^^ !^ "|}"
    )
  | Field (e, x) -> to_coq true e ^-^ !^ ".(" ^-^ PathName.to_coq x ^-^ !^ ")"
  | IfThenElse (e1, e2, e3) ->
    Pp.parens paren @@ nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
  | Module (nb_of_existential_variables, fields) ->
    Pp.parens paren @@ nest (
      !^ "existT" ^^
      begin match nb_of_existential_variables with
      | 0 -> !^ "(fun _ => _)"
      |_ -> !^ "_"
      end ^^
      begin match to_coq_n_underscores nb_of_existential_variables with
      | [] -> !^ "tt"
      | [_] -> !^ "_"
      | n_underscores -> brakets (separate (!^ "," ^^ space) n_underscores)
      end ^^
      group (
        !^ "{|" ^^ newline ^^
        indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, nb_free_vars, e) ->
          nest (
            group (
              nest (
                PathName.to_coq x ^^
                begin match nb_free_vars with
                | 0 -> empty
                | _ -> braces (nest (separate space (to_coq_n_underscores nb_free_vars)))
                end
              ) ^^
              !^ ":="
            ) ^^
            to_coq false e)
          )
        )) ^^ newline ^^
        !^ "|}"
      )
    )
  | ModuleNested fields ->
    Pp.parens paren @@ nest (
      !^ "{|" ^^ newline ^^
      indent @@ separate (!^ ";" ^^ newline) (fields |> List.map (fun (error_message, x, e) ->
        (match error_message with
        | None -> empty
        | Some error_message -> Error.to_comment error_message ^^ newline) ^^
        nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e)
      )) ^^ newline ^^
      !^ "|}"
    )
  | Functor (x, typ, e) ->
    Pp.parens paren @@ nest (
      !^ "fun" ^^
      parens (nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None typ)) ^^
      !^ "=>" ^^ to_coq false e
    )
  | TypeAnnotation (e, typ) ->
    parens @@ nest (to_coq false e ^^ !^ ":" ^^ Type.to_coq None None typ)
  | Error message -> !^ message
  | ErrorArray es -> OCaml.list (to_coq false) es
  | ErrorTyp typ -> Pp.parens paren @@ Type.to_coq None None typ
  | ErrorMessage (e, error_message) ->
    group (Error.to_comment error_message ^^ newline ^^ to_coq paren e)

and cast_existentials
  (existential_cast : match_existential_cast option)
  (e : t)
  : SmartPrint.t =
  let e =
    match existential_cast with
    | Some { return_typ; cast_with_axioms = true; _ } ->
      nest (
        !^ "obj_magic" ^^ Type.to_coq None (Some Type.Context.Apply) return_typ ^^
        to_coq true e
      )
    | _ -> to_coq false e in
  match existential_cast with
  | None
  | Some { bound_vars = []; _ }
  | Some { new_typ_vars = []; cast_with_axioms = false; _ } -> e
  | Some { new_typ_vars; bound_vars; cast_with_axioms; _ } ->
    let existential_names =
      Pp.primitive_tuple (List.map Name.to_coq new_typ_vars) in
    let existential_names_pattern =
      Pp.primitive_tuple_pattern (List.map Name.to_coq new_typ_vars) in
    let variable_names =
      Pp.primitive_tuple (bound_vars |> List.map (fun (name, _) ->
        Name.to_coq name
      )) in
    let variable_typ =
      Pp.primitive_tuple_type (bound_vars |> List.map (fun (_, typ) ->
        Type.to_coq None (Some Type.Context.Apply) typ
      )) in
    nest (
      !^ "let" ^^
      !^ "'existT" ^^ !^ "_" ^^ existential_names ^^
      variable_names ^^ !^ ":=" ^^
      nest (
        begin if cast_with_axioms then
          !^ "obj_magic_exists"
        else
          !^ "existT"
        end ^^
        parens (nest (
          !^ "fun" ^^ existential_names_pattern ^^
          (* TODO: try to remove this annotation once in Coq 8.11 *)
          begin match new_typ_vars with
          | [_] -> !^ ":" ^^ !^ "Set"
          | _ -> empty
          end ^^
          !^ "=>" ^^ variable_typ
        )) ^^
        begin if cast_with_axioms then
          empty
        else
          !^ "_"
        end ^^
        variable_names
      ) ^^ !^ "in" ^^ newline ^^
      e
    )
