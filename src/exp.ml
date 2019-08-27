(** An expression. *)
open Typedtree
open Types
open Sexplib.Std
open SmartPrint

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
let rec of_expression (typ_vars : Name.t Name.Map.t) (e : expression) : t =
  let l = Loc.of_location e.exp_loc in
  let env = Envaux.env_of_only_summary e.exp_env in
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
    let x = MixedPath.of_path env l path in
    Variable x
  | Texp_constant constant -> Constant (Constant.of_constant l constant)
  | Texp_let (_, [{ vb_pat = p; vb_expr = e1 }], e2)
    when (match e1.exp_desc with
    | Texp_function _ -> false
    | _ -> true) ->
    let p = Pattern.of_pattern p in
    let e1 = of_expression typ_vars e1 in
    (match p with
    | Pattern.Variable x ->
      let e2 = of_expression typ_vars e2 in
      LetVar (x, e1, e2)
    | _ ->
      let e2 = of_expression typ_vars e2 in
      Match (e1, [p, e2]))
  | Texp_let (is_rec, cases, e) ->
    let def = import_let_fun l typ_vars is_rec cases in
    let e = of_expression typ_vars e in
    LetFun (def, e)
  | Texp_function { cases = [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}] }
  | Texp_function { cases = [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}] } ->
    let x = Name.of_ident x in
    Function (x, of_expression typ_vars e)
  | Texp_function { cases = cases } ->
    let (x, e) = open_cases typ_vars cases in
    Function (x, e)
  | Texp_apply (e_f, e_xs) ->
    let e_f = of_expression typ_vars e_f in
    let e_xs = List.map (fun (_, e_x) ->
      match e_x with
      | Some e_x -> of_expression typ_vars e_x
      | None -> Error.raise l "expected an argument") e_xs in
    Apply (e_f, e_xs)
  | Texp_match (e, cases, _, _) ->
    let e = of_expression typ_vars e in
    let cases = cases |> List.map (fun {c_lhs = p; c_guard = g; c_rhs = e} ->
      if g <> None then Error.warn l "Guard on pattern ignored.";
      let p = Pattern.of_pattern p in
      (p, of_expression typ_vars e)) in
    Match (e, cases)
  | Texp_tuple es -> Tuple (List.map (of_expression typ_vars) es)
  | Texp_construct (x, _, es) ->
    let x = PathName.of_loc x in
    Constructor (x, List.map (of_expression typ_vars) es)
  | Texp_record { fields = fields; extended_expression = None } ->
    Record (Array.to_list fields |> List.map (fun (label, definition) ->
      let (x, e) =
        match definition with
        | Kept _ -> Error.raise l "Records with overwriting not handled."
        | Overridden (loc, e) -> (loc, e) in
      let x = PathName.of_loc x in
      (x, of_expression typ_vars e)))
  | Texp_field (e, x, _) ->
    let x = PathName.of_loc x in
    Field (of_expression typ_vars e, x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Tuple []
      | Some e3 -> of_expression typ_vars e3 in
    IfThenElse (of_expression typ_vars e1, of_expression typ_vars e2, e3)
  | Texp_sequence _ ->
    Error.raise l (
      "Sequences of instructions are not handled (operator \";\").\n\n" ^
      "Sequences are usually there to sequence side-effects. " ^
      "You could rewrite this code without side-effects or use a monad."
    )
  | Texp_try _ ->
    Error.raise l (
      "Try-with and exceptions are not handled.\n\n" ^
      "You could use sum types (\"option\", \"result\", ...) to represent an error case."
    )
  | Texp_setfield _ -> Error.raise l "Set field not handled."
  | Texp_array _ -> Error.raise l "Arrays not handled."
  | Texp_while _ -> Error.raise l "While loops not handled."
  | Texp_for _ -> Error.raise l "For loops not handled."
  | Texp_assert e -> Error.raise l "Assert instruction is not handled."
  | _ -> Error.raise l "Expression not handled."

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases (typ_vars : Name.t Name.Map.t) (cases : case list) : Name.t * t =
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
    let p = Pattern.of_pattern p in
    (p, of_expression typ_vars e)) in
  let name = Name.of_string "function_parameter" in
  (name, Match (Variable (MixedPath.of_name name), cases))

and import_let_fun (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (is_rec : Asttypes.rec_flag)
  (cases : value_binding list)
  : t Definition.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  let cases = cases |> List.map (fun { vb_pat = p; vb_expr = e } ->
    let loc = Loc.of_location p.pat_loc in
    let p = Pattern.of_pattern p in
    match p with
    | Pattern.Variable x -> (x, e, loc)
    | _ -> Error.raise loc "A variable name instead of a pattern was expected.") in
  let cases = cases |> List.map (fun (x, e, loc) ->
    let env = Envaux.env_of_only_summary e.exp_env in
    let (e_typ, typ_vars, new_typ_vars) =
      Type.of_type_expr_new_typ_vars env loc typ_vars e.exp_type in
    let e = of_expression typ_vars e in
    let (args_names, e_body) = open_function e in
    let (args_typs, e_body_typ) =
      Type.open_type e_typ (List.length args_names) in
    let header = {
      Header.name = x;
      typ_vars = Name.Set.elements new_typ_vars;
      args = List.combine args_names args_typs;
      typ = Some e_body_typ } in
    (header, e_body)) in
  {
    Definition.is_rec = is_rec;
    cases = cases;
  }

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
