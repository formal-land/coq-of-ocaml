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
  | Match of t * (Pattern.t * t) list
    (** Match an expression to a list of patterns. *)
  | Record of (PathName.t * t) list
    (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t (** Access to a field of a record. *)
  | IfThenElse of t * t * t (** The "else" part may be unit. *)
  | Module of Type.t list * (PathName.t * t) list (** The value of a first-class module. *)
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
    all3
      (Pattern.of_pattern p)
      (of_expression typ_vars e1)
      (of_expression typ_vars e2) >>= fun (p, e1, e2) ->
    begin match p with
    | Pattern.Variable x -> return (LetVar (x, e1, e2))
    | _ -> return (Match (e1, [p, e2]))
    end
  | Texp_let (is_rec, cases, e) ->
    all2
      (import_let_fun typ_vars is_rec cases)
      (of_expression typ_vars e) >>= fun (def, e) ->
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
    all2
      (of_expression typ_vars e_f)
      (e_xs |> Monad.List.map (fun (_, e_x) ->
        match e_x with
        | Some e_x -> of_expression typ_vars e_x
        | None -> raise "expected an argument")
      ) >>= fun (e_f, e_xs) ->
    return (Apply (e_f, e_xs))
  | Texp_match (e, cases, _, _) ->
    all2
      (of_expression typ_vars e)
      (cases |> Monad.List.map (fun {c_lhs = p; c_guard = g; c_rhs = e} ->
        match g with
        | Some _ -> raise "Guard on pattern ignored."
        | None -> all2 (Pattern.of_pattern p) (of_expression typ_vars e)
      )) >>= fun (e, cases) ->
    return (Match (e, cases))
  | Texp_tuple es ->
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    return (Tuple es)
  | Texp_construct (x, _, es) ->
    let x = PathName.of_loc x in
    Monad.List.map (of_expression typ_vars) es >>= fun es ->
    return (Constructor (x, es))
  | Texp_record { fields = fields; extended_expression = None } ->
    (Array.to_list fields |> Monad.List.map (fun (label, definition) ->
      (match definition with
      | Kept _ -> raise "Records with overwriting are not handled"
      | Overridden (loc, e) -> return (loc, e)) >>= fun (x, e) ->
      let x = PathName.of_loc x in
      of_expression typ_vars e >>= fun e ->
      return (x, e)
    )) >>= fun fields ->
    return (Record fields)
  | Texp_field (e, x, _) ->
    let x = PathName.of_loc x in
    of_expression typ_vars e >>= fun e ->
    return (Field (e, x))
  | Texp_ifthenelse (e1, e2, e3) ->
    all3
      (of_expression typ_vars e1)
      (of_expression typ_vars e2)
      (match e3 with
      | None -> return (Tuple [])
      | Some e3 -> of_expression typ_vars e3) >>= fun (e1, e2, e3) ->
    return (IfThenElse (e1, e2, e3))
  | Texp_sequence _ ->
    raise (
      "Sequences of instructions are not handled (operator \";\").\n\n" ^
      "Sequences are usually there to sequence side-effects. " ^
      "You could rewrite this code without side-effects or use a monad."
    )
  | Texp_try _ ->
    raise (
      "Try-with and exceptions are not handled.\n\n" ^
      "You could use sum types (\"option\", \"result\", ...) to represent an error case."
    )
  | Texp_setfield _ -> raise "Set field not handled."
  | Texp_array _ -> raise "Arrays not handled."
  | Texp_while _ -> raise "While loops not handled."
  | Texp_for _ -> raise "For loops not handled."
  | Texp_assert e -> raise "Assert instruction is not handled."
  | _ -> raise "Expression not handled."))

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases
  (typ_vars : Name.t Name.Map.t)
  (cases : case list)
  : (Name.t * t) Monad.t =
  (cases |> Monad.List.map (fun {c_lhs = p; c_rhs = e} ->
    all2 (Pattern.of_pattern p) (of_expression typ_vars e)
  )) >>= fun cases ->
  let name = Name.of_string "function_parameter" in
  return (name, Match (Variable (MixedPath.of_name name), cases))

and import_let_fun
  (typ_vars : Name.t Name.Map.t)
  (is_rec : Asttypes.rec_flag)
  (cases : value_binding list)
  : t Definition.t Monad.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  (cases |> Monad.List.map (fun { vb_pat = p; vb_expr = e } ->
    set_env e.exp_env (
    set_loc (Loc.of_location p.pat_loc) (
    all2
      (Pattern.of_pattern p >>= fun p ->
      (match p with
      | Pattern.Variable x -> return x
      | _ -> raise "A variable name instead of a pattern was expected."
      ))
      (Type.of_type_expr_new_typ_vars typ_vars e.exp_type)
    >>= fun (x, (e_typ, typ_vars, new_typ_vars)) ->
    of_expression typ_vars e >>= fun e ->
    let (args_names, e_body) = open_function e in
    let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
    let header = {
      Header.name = x;
      typ_vars = Name.Set.elements new_typ_vars;
      args = List.combine args_names args_typs;
      typ = Some e_body_typ
    } in
    return (header, e_body))
  ))) >>= fun cases ->
  return {
    Definition.is_rec = is_rec;
    cases = cases;
  }

let of_structure (signature_path : Path.t) (structure : structure) : t Monad.t =
  (structure.str_items |> Monad.List.filter_map (fun item ->
    set_loc (Loc.of_location item.str_loc) (
    match item.str_desc with
    | Tstr_eval _ -> raise "Eval not handled"
    | Tstr_value (rec_flag, cases) ->
      import_let_fun Name.Map.empty rec_flag cases >>= fun def ->
      begin match def with
      | { is_rec = Recursivity.New true } ->
        raise "Recursivity not handled in first-class module values"
      | { cases = [(header, value)] } ->
        begin match header with
        | { name; typ_vars = []; args = [] } ->
          let path_name = PathName.of_path_and_name signature_path name in
          return (Some (path_name, value))
        | _ ->
          raise "This kind of definition of value for first-class modules is not handled (yet)"
        end
      | _ -> raise "Mutual definitions not handled in first-class module values"
      end
    | Tstr_primitive _ -> raise "Primitive not handled"
    | Tstr_type _ -> return None
    | Tstr_typext _ -> raise "Type extension not handled"
    | Tstr_exception _ -> raise "Exception not handled"
    | Tstr_module _ -> raise "Modules in first-class module values not handled (yet)"
    | Tstr_recmodule _ -> raise "Recursive modules not handled"
    | Tstr_modtype _ ->
      raise "Definition of signatures inside first-class module value is not handled"
    | Tstr_open _ -> raise "Open not handled in first-class module value"
    | Tstr_class _ -> raise "Object oriented programming not handled"
    | Tstr_class_type _ -> raise "Object oriented programming not handled"
    | Tstr_include _ -> raise "Include is not handled inside first-class module values"
    | Tstr_attribute _ -> return None)
  )) >>= fun fields ->
  return (Module ([], fields))

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
    let firt_case = ref true in (* TODO: say that 'let rec and' is not supported (yet?) inside expressions. *)
    Pp.parens paren @@ nest (separate newline
      (def.Definition.cases |> List.map (fun (header, e) ->
        (if !firt_case then (
          firt_case := false;
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
          parens (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false x_typ)))) ^^
        (match header.Header.typ with
        | None -> empty
        | Some typ -> !^ ": " ^-^ Type.to_coq false typ) ^-^
        !^ " :=" ^^ newline ^^
        indent (to_coq false e))) ^^ !^ "in" ^^ newline ^^ to_coq false e)
  | Match (e, cases) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline))) ^^
      !^ "end")
  | Record (fields) ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
      nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))) ^^ !^ "|}")
  | Field (e, x) -> Pp.parens paren @@ nest (PathName.to_coq x ^^ to_coq true e)
  | IfThenElse (e1, e2, e3) ->
    Pp.parens paren @@ nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
  | Module (existential_typs, fields) ->
    Pp.parens paren @@ nest (
      !^ "existT" ^^ !^ "_" ^^
      (match existential_typs with
      | [] -> !^ "unit"
      | [existential_typ] -> Type.to_coq true existential_typ
      | _ ->
        parens @@ nest @@ separate (!^ "," ^^ space) (
          existential_typs |> List.map (fun existential_typ ->
            Type.to_coq false existential_typ ^^ !^ ":" ^^ !^ "Type"
          )
        )
      ) ^^
      nest (
        !^ "{|" ^^
        separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
          nest (PathName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))
        ) ^^
        !^ "|}"
      )
    )
