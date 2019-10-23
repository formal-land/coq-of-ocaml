(** An expression. *)
open Typedtree
open Types
open Sexplib.Std
open SmartPrint
open Monad.Notations

module Header = struct
  type t = {
    name : Name.t;
    typ_vars : Name.t list;
    args : (Name.t * Type.t) list;
    typ : Type.t option }
    [@@deriving sexp]
end

module Definition = struct
  type 'a t = {
    is_rec : Recursivity.t;
    cases : (Header.t * 'a) list }
    [@@deriving sexp]
end

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type t =
  | Constant of Constant.t
  | Variable of MixedPath.t
  | Tuple of t list (** A tuple of expressions. *)
  | Constructor of PathName.t * t list
    (** A constructor name and a list of arguments. *)
  | Apply of t * t list (** An application. *)
  | Function of Name.t * t (** An argument name and a body. *)
  | LetVar of Name.t * t * t
  | LetFun of t Definition.t * t
  | Match of t * (Pattern.t * t) list * t option
    (** Match an expression to a list of patterns. *)
  | Record of (PathName.t * t) list
    (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t (** Access to a field of a record. *)
  | IfThenElse of t * t * t (** The "else" part may be unit. *)
  | Module of (PathName.t * t) list (** The value of a first-class module. *)
  | ModuleNested of (PathName.t * t) list (** The value of a first-class module inside another module (no existentials). *)
  | ModuleUnpack of t (** Open a first-class module *)
  | Error of string (** An error message for unhandled expressions. *)
  | ErrorSeq of t * t (** A sequence of two expressions (an error in Coq). *)
  [@@deriving sexp]

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (typ_vars : Name.t Name.Map.t) (e : expression) : t Monad.t =
  set_env e.exp_env (
  set_loc (Loc.of_location e.exp_loc) (
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
    MixedPath.of_path path >>= fun x ->
    return (Variable x)
  | Texp_constant constant ->
    Constant.of_constant constant >>= fun constant ->
    return (Constant constant)
  | Texp_let (_, [{ vb_pat = p; vb_expr = e1 }], e2)
    when (match e1.exp_desc with
    | Texp_function _ -> false
    | _ -> true) ->
    Pattern.of_pattern p >>= fun p ->
    of_expression typ_vars e1 >>= fun e1 ->
    of_expression typ_vars e2 >>= fun e2 ->
    begin match p with
    | Pattern.Variable x -> return (LetVar (x, e1, e2))
    | _ -> return (Match (e1, [p, e2], None))
    end
  | Texp_let (is_rec, cases, e) ->
    import_let_fun typ_vars is_rec cases >>= fun def ->
    of_expression typ_vars e >>= fun e ->
    return (LetFun (def, e))
  | Texp_function { cases = [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}] }
  | Texp_function { cases = [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}] } ->
    let x = Name.of_ident x in
    of_expression typ_vars e >>= fun e ->
    return (Function (x, e))
  | Texp_function { cases = cases } ->
    open_cases typ_vars cases >>= fun (x, e) ->
    return (Function (x, e))
  | Texp_apply (e_f, e_xs) ->
    of_expression typ_vars e_f >>= fun e_f ->
    (e_xs |> Monad.List.map (fun (_, e_x) ->
      match e_x with
      | Some e_x -> of_expression typ_vars e_x
      | None -> raise (Error "expected_argument") Unexpected "expected an argument")
    ) >>= fun e_xs ->
    return (Apply (e_f, e_xs))
  | Texp_match (e, cases, exception_cases, _) ->
    of_expression typ_vars e >>= fun e ->
    (cases |> Monad.List.filter_map (fun {c_lhs; c_guard; c_rhs} ->
      set_loc (Loc.of_location c_lhs.pat_loc) (
      match c_guard with
      | Some _ -> raise None NotSupported "Guard on pattern not supported"
      | None ->
        Pattern.of_pattern c_lhs >>= fun pattern ->
        of_expression typ_vars c_rhs >>= fun c_rhs ->
        return (Some (pattern, c_rhs)))
    )) >>= fun cases ->
    (exception_cases |> Monad.List.filter_map (fun {c_lhs; c_guard; c_rhs} ->
      set_loc (Loc.of_location c_lhs.pat_loc) (
      match c_guard with
      | Some guard_exp ->
        of_expression typ_vars guard_exp >>= fun guard_exp ->
        begin match guard_exp with
        | Constructor ({ PathName.path = []; base = "false" }, []) ->
          of_expression typ_vars c_rhs >>= fun c_rhs ->
          return (Some c_rhs)
        | _ -> raise None Unexpected "Expected `false` as guard on the exception case to represent the default GADT case"
        end
      | None ->
        raise None NotSupported (
          "Pattern-matching on exceptions not supported\n\n" ^
          "Only the special case `| exception _ when false -> ...` is supported for default value of GADT pattern-matching"
        ))
    )) >>= fun default_values ->
    let default_value =
      match default_values with
      | [default_value] -> Some default_value
      | _ -> None in
    return (Match (e, cases, default_value))
  | Texp_tuple es ->
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    return (Tuple es)
  | Texp_construct (x, _, es) ->
    let x = PathName.of_loc x in
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    return (Constructor (x, es))
  | Texp_variant _ -> raise (Error "variant") NotSupported "Variants not supported"
  | Texp_record { fields = fields; extended_expression = None } ->
    (Array.to_list fields |> Monad.List.filter_map (fun (label, definition) ->
      (match definition with
      | Kept _ ->
        raise None NotSupported "Records with overwriting are not handled"
      | Overridden (loc, e) -> return (Some (loc, e))) >>= fun x_e ->
      match x_e with
      | None -> return None
      | Some (x, e) ->
        let x = PathName.of_loc x in
        of_expression typ_vars e >>= fun e ->
        return (Some (x, e))
    )) >>= fun fields ->
    return (Record fields)
  | Texp_record _ -> raise (Error "record") NotSupported "This kind of record expression is not supported"
  | Texp_field (e, x, _) ->
    let x = PathName.of_loc x in
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
    of_expression typ_vars e1 >>= fun e1 ->
    of_expression typ_vars e2 >>= fun e2 ->
    raise
      (ErrorSeq (e1, e2))
      SideEffect
      (
        "Sequences of instructions are not handled (operator \";\")\n\n" ^
        "Alternative: use a monad to sequence side-effects."
      )
  | Texp_try _ ->
    raise (Error "try") SideEffect (
      "Try-with and exceptions are not handled.\n\n" ^
      "Alternative: use sum types (\"option\", \"result\", ...) to represent an error case."
    )
  | Texp_setfield _ -> raise (Error "set_field") SideEffect "Set field not handled."
  | Texp_array es ->
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    raise (Tuple es) NotSupported "Arrays not handled."
  | Texp_while _ -> raise (Error "while") SideEffect "While loops not handled."
  | Texp_for _ -> raise (Error "for") SideEffect "For loops not handled."
  | Texp_send _ -> raise (Error "send") NotSupported "Sending method message is not handled"
  | Texp_new _ -> raise (Error "new") NotSupported "Creation of new objects is not handled"
  | Texp_instvar _ ->
    raise (Error "instance_variable") NotSupported "Creating an instance variable is not handled"
  | Texp_setinstvar _ ->
    raise (Error "set_instance_variable") SideEffect "Setting an instance variable is not handled"
  | Texp_override _ -> raise (Error "override") NotSupported "Overriding is not handled"
  | Texp_letmodule (x, _, module_expr, e) ->
    let x = Name.of_ident x in
    of_module_expr typ_vars module_expr None >>= fun value ->
    of_expression typ_vars e >>= fun e ->
    return (LetVar (x, value, e))
  | Texp_letexception _ -> raise (Error "let_exception") SideEffect "Let of exception is not handled"
  | Texp_assert e ->
    of_expression typ_vars e >>= fun e ->
    raise e SideEffect "Assert instruction is not handled."
  | Texp_lazy e ->
    of_expression typ_vars e >>= fun e ->
    raise e SideEffect "Lazy expressions are not handled"
  | Texp_object _ -> raise (Error "object") NotSupported "Creation of objects is not handled"
  | Texp_pack module_expr -> of_module_expr typ_vars module_expr None
  | Texp_unreachable ->
    raise (Error "unreachable") NotSupported "Unreachable expressions are not supported"
  | Texp_extension_constructor _ ->
    raise (Error "extension") NotSupported "Construction of extensions is not handled"))

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases
  (typ_vars : Name.t Name.Map.t)
  (cases : case list)
  : (Name.t * t) Monad.t =
  (cases |> Monad.List.map (fun {c_lhs = p; c_rhs = e} ->
    Pattern.of_pattern p >>= fun pattern ->
    of_expression typ_vars e >>= fun e ->
    return (pattern, e)
  )) >>= fun cases ->
  let name = Name.of_string "function_parameter" in
  return (name, Match (Variable (MixedPath.of_name name), cases, None))

and import_let_fun
  (typ_vars : Name.t Name.Map.t)
  (is_rec : Asttypes.rec_flag)
  (cases : value_binding list)
  : t Definition.t Monad.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  (cases |> Monad.List.filter_map (fun { vb_pat = p; vb_expr = e } ->
    set_env e.exp_env (
    set_loc (Loc.of_location p.pat_loc) (
    Pattern.of_pattern p >>= fun p ->
    (match p with
    | Pattern.Any -> return None
    | Pattern.Variable x -> return (Some x)
    | _ -> raise None Unexpected "A variable name instead of a pattern was expected."
    ) >>= fun x ->
    Type.of_typ_expr true typ_vars e.exp_type >>= fun (e_typ, typ_vars, new_typ_vars) ->
    match x with
    | None -> return None
    | Some x ->
      of_expression typ_vars e >>= fun e ->
      let (args_names, e_body) = open_function e in
      let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
      let header = {
        Header.name = x;
        typ_vars = Name.Set.elements new_typ_vars;
        args = List.combine args_names args_typs;
        typ = Some e_body_typ
      } in
      return (Some (header, e_body))
    )
  ))) >>= fun cases ->
  return {
    Definition.is_rec = is_rec;
    cases = cases;
  }

and of_module_expr
  (typ_vars : Name.t Name.Map.t)
  (module_expr : module_expr)
  (module_type : Types.module_type option)
  : t Monad.t =
  let { mod_desc; mod_env; mod_loc; mod_type } = module_expr in
  set_env mod_env (
  set_loc (Loc.of_location mod_loc) (
  match mod_desc with
  | Tmod_ident (path, _) ->
    MixedPath.of_path path >>= fun path ->
    return (Variable path)
  | Tmod_structure structure ->
    let module_type =
      match module_type with
      | Some module_type -> module_type
      | None -> mod_type in
    IsFirstClassModule.is_module_typ_first_class module_type >>= fun is_first_class ->
    begin match is_first_class with
    | Some signature_path -> of_structure typ_vars signature_path structure
    | None ->
      raise
        (Error "module_of_unknown_signature_name")
        Unexpected
        "The signature name of this module could not be found"
    end
  | Tmod_functor _ ->
    raise
      (Error "unsupported_functor")
      NotSupported
      "Functors are not supported for first-class module values"
  | Tmod_apply _ ->
    raise
      (Error "unsupported_functor_application")
      NotSupported
      "Applications of functors are not supported for first-class module values"
  | Tmod_constraint (module_expr, mod_type, _, _) ->
    let module_type =
      match module_type with
      | Some _ -> module_type
      | None -> Some mod_type in
    of_module_expr typ_vars module_expr module_type
  | Tmod_unpack (e, _) ->
    of_expression typ_vars e >>= fun e ->
    return (ModuleUnpack e)
  ))

and of_structure
  (typ_vars : Name.t Name.Map.t)
  (signature_path : Path.t)
  (structure : structure)
  : t Monad.t =
  (structure.str_items |> Monad.List.filter_map (fun item ->
    set_env item.str_env (
    set_loc (Loc.of_location item.str_loc) (
    match item.str_desc with
    | Tstr_eval _ -> raise None SideEffect "Top-level evaluation is not handled"
    | Tstr_value (rec_flag, cases) ->
      import_let_fun Name.Map.empty rec_flag cases >>= fun def ->
      begin match def with
      | { is_rec = Recursivity.New true } ->
        raise None NotSupported "Recursivity not handled in first-class module values"
      | { cases = [(header, value)] } ->
        begin match header with
        | { name; typ_vars = []; args = [] } ->
          return (Some (name, value))
        | _ ->
          raise
            None
            NotSupported
            "This kind of definition of value for first-class modules is not handled (yet)"
        end
      | _ -> raise None NotSupported "Mutual definitions not handled in first-class module values"
      end
    | Tstr_primitive _ -> raise None NotSupported "Primitive not handled"
    | Tstr_type _ -> return None
    | Tstr_typext _ -> raise None NotSupported "Type extension not handled"
    | Tstr_exception _ -> raise None SideEffect "Exception not handled"
    | Tstr_module { mb_id; mb_expr } ->
      let name = Name.of_ident mb_id in
      of_module_expr typ_vars mb_expr None >>= fun value ->
      return (Some (name, value))
    | Tstr_recmodule _ -> raise None NotSupported "Recursive modules not handled"
    | Tstr_modtype _ ->
      raise None NotSupported "Definition of signatures inside first-class module value is not handled"
    | Tstr_open _ -> raise None NotSupported "Open not handled in first-class module value"
    | Tstr_class _ -> raise None NotSupported "Object oriented programming not handled"
    | Tstr_class_type _ -> raise None NotSupported "Object oriented programming not handled"
    | Tstr_include _ -> raise None NotSupported "Include is not handled inside first-class module values"
    | Tstr_attribute _ -> return None)
  ))) >>= fun fields ->
  let fields = fields |> List.map (fun (name, field) -> (PathName.of_path_and_name signature_path name, field)) in
  return (Module fields)

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq c
  | Variable x -> MixedPath.to_coq x
  | Tuple es ->
    if es = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (x, es) ->
    if es = [] then
      PathName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space
        (PathName.to_coq x :: List.map (to_coq true) es)
  | Apply (e_f, e_xs) ->
    Pp.parens paren @@ nest @@ (separate space (List.map (to_coq true) (e_f :: e_xs)))
  | Function (x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | LetVar (x, e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^-^ !^ " :=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | LetFun (def, e) ->
    (* TODO: say that 'let rec and' is not supported (yet?) inside expressions. *)
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
          !^ ":" ^^ !^ "Type")) ^^
        group (separate space (header.Header.args |> List.map (fun (x, x_typ) ->
          parens (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None false x_typ)))) ^^
        (match header.Header.typ with
        | None -> empty
        | Some typ -> !^ ": " ^-^ Type.to_coq None false typ) ^-^
        !^ " :=" ^^ newline ^^
        indent (to_coq false e))) ^^ !^ "in" ^^ newline ^^ to_coq false e)
  | Match (e, cases, default_value) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline)
      )) ^^
      (match default_value with
      | None -> empty
      | Some default_value -> nest (!^ "|" ^^ !^ "_" ^^ !^ "=>" ^^ to_coq false default_value ^^ newline)
      ) ^^
      !^ "end")
  | Record fields ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
      nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))) ^^ !^ "|}")
  | Field (e, x) -> Pp.parens paren @@ nest (PathName.to_coq x ^^ to_coq true e)
  | IfThenElse (e1, e2, e3) ->
    Pp.parens paren @@ nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
  | Module fields ->
    Pp.parens paren @@ nest (
      !^ "existT" ^^ !^ "_" ^^ !^ "_" ^^
      nest (
        !^ "{|" ^^ newline ^^
        indent @@ separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, e) ->
          nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))
        ) ^^ newline ^^
        !^ "|}"
      )
    )
  | ModuleNested fields ->
    Pp.parens paren @@ nest (
      !^ "{|" ^^ newline ^^
      indent @@ separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, e) ->
        nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))
      ) ^^ newline ^^
      !^ "|}"
    )
  | ModuleUnpack e -> Pp.parens paren @@ nest (!^ "projT2" ^^ to_coq true e)
  | Error message -> !^ message
  | ErrorSeq (e1, e2) ->
    Pp.parens paren @@ nest (to_coq false e1 ^-^ !^ ";" ^^ newline ^^ to_coq false e2)
