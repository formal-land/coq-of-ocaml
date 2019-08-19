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

  let pp (header : t) : SmartPrint.t =
    OCaml.tuple [
      Name.pp header.name; OCaml.list Name.pp header.typ_vars;
      OCaml.list (fun (x, typ) -> OCaml.tuple [Name.pp x; Type.pp typ])
        header.args;
      OCaml.option Type.pp header.typ]

  let env_in_header (header : t) (env : 'a FullEnvi.t) (v : 'a)
    : 'a FullEnvi.t =
    List.fold_left (fun env (x, _) -> FullEnvi.add_var [] x v env)
      env header.args
end

module Definition = struct
  type 'a t = {
    is_rec : Recursivity.t;
    cases : (Header.t * 'a) list }
    [@@deriving sexp]

  let pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
    OCaml.tuple [Recursivity.pp def.is_rec;
      def.cases |> OCaml.list (fun (header, e) ->
        OCaml.tuple [Header.pp header; pp_a e])]

  let names (def : 'a t) : Name.t list =
    List.map (fun (header, _) -> header.Header.name) def.cases

  let env_after_def (def : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    List.fold_left (fun env x -> FullEnvi.add_var [] x () env)
      env (names def)

  let env_in_def (def : 'a t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    if Recursivity.to_bool def.is_rec then
      env_after_def def env
    else
      env
end

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type 'a t =
  | Constant of 'a * Constant.t
  | Variable of 'a * BoundName.t
  | Tuple of 'a * 'a t list (** A tuple of expressions. *)
  | Constructor of 'a * BoundName.t * 'a t list
    (** A constructor name and a list of arguments. *)
  | Apply of 'a * 'a t * 'a t list (** An application. *)
  | Function of 'a * Name.t * 'a t (** An argument name and a body. *)
  | LetVar of 'a * Name.t * 'a t * 'a t
  | LetFun of 'a * 'a t Definition.t * 'a t
  | Match of 'a * 'a t * (Pattern.t * 'a t) list
    (** Match an expression to a list of patterns. *)
  | Record of 'a * (BoundName.t * 'a t) list
    (** Construct a record giving an expression for each field. *)
  | Field of 'a * 'a t * BoundName.t (** Access to a field of a record. *)
  | IfThenElse of 'a * 'a t * 'a t * 'a t (** The "else" part may be unit. *)
  [@@deriving sexp]

let rec pp (pp_a : 'a -> SmartPrint.t) (e : 'a t) : SmartPrint.t =
  let pp = pp pp_a in
  match e with
  | Constant (a, c) ->
    nest (!^ "Constant" ^^ OCaml.tuple [pp_a a; Constant.pp c])
  | Variable (a, x) ->
    nest (!^ "Variable" ^^ OCaml.tuple [pp_a a; BoundName.pp x])
  | Tuple (a, es) ->
    nest (!^ "Tuple" ^^ OCaml.tuple (pp_a a :: List.map pp es))
  | Constructor (a, x, es) ->
    nest (!^ "Constructor" ^^
      OCaml.tuple (pp_a a :: BoundName.pp x :: List.map pp es))
  | Apply (a, e_f, e_xs) ->
    nest (!^ "Apply" ^^ OCaml.tuple [pp_a a; pp e_f; OCaml.list pp e_xs])
  | Function (a, x, e) ->
    nest (!^ "Function" ^^ OCaml.tuple [pp_a a; Name.pp x; pp e])
  | LetVar (a, x, e1, e2) ->
    nest (!^ "LetVar" ^^
      pp_a a ^^ Name.pp x ^^ !^ "=" ^^ pp e1 ^^ !^ "in" ^^ newline ^^
      pp e2)
  | LetFun (a, def, e2) ->
    nest (!^ "LetFun" ^^ pp_a a ^^ newline ^^ indent (Definition.pp pp def) ^^
      !^ "in" ^^ newline ^^ pp e2)
  | Match (a, e, cases) ->
    nest (!^ "Match" ^^ OCaml.tuple [pp_a a; pp e;
      cases |> OCaml.list (fun (p, e) ->
        nest @@ parens (Pattern.pp p ^-^ !^ "," ^^ pp e))])
  | Record (a, fields) ->
    nest (!^ "Record" ^^
      OCaml.tuple (pp_a a :: (fields |> List.map (fun (x, e) ->
        nest @@ parens (BoundName.pp x ^-^ !^ "," ^^ pp e)))))
  | Field (a, e, x) ->
    nest (!^ "Field" ^^ OCaml.tuple [pp_a a; pp e; BoundName.pp x])
  | IfThenElse (a, e1, e2, e3) ->
    nest (!^ "IfThenElse" ^^ OCaml.tuple [pp_a a; pp e1; pp e2; pp e3])

let annotation (e : 'a t) : 'a =
  match e with
  | Constant (a, _) | Variable (a, _) | Tuple (a, _) | Constructor (a, _, _)
  | Apply (a, _, _) | Function (a, _, _) | LetVar (a, _, _, _)
  | LetFun (a, _, _) | Match (a, _, _) | Record (a, _) | Field (a, _, _)
  | IfThenElse (a, _, _, _) -> a

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : 'a t) : Name.t list * 'a t =
  match e with
  | Function (_, x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (env : unit FullEnvi.t) (typ_vars : Name.t Name.Map.t)
  (e : expression) : Loc.t t =
  let l = Loc.of_location e.exp_loc in
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
    let x = Envi.bound_name l (PathName.of_path l path) env.FullEnvi.vars in
    Variable (l, x)
  | Texp_constant constant -> Constant (l, Constant.of_constant l constant)
  | Texp_let (_, [{ vb_pat = p; vb_expr = e1 }], e2)
    when (match e1.exp_desc with
    | Texp_function _ -> false
    | _ -> true) ->
    let p = Pattern.of_pattern env p in
    let e1 = of_expression env typ_vars e1 in
    (match p with
    | Pattern.Variable x ->
      let env = FullEnvi.add_var [] x () env in
      let e2 = of_expression env typ_vars e2 in
      LetVar (l, x, e1, e2)
    | _ ->
      let env = Pattern.add_to_env p env in
      let e2 = of_expression env typ_vars e2 in
      Match (l, e1, [p, e2]))
  | Texp_let (is_rec, cases, e) ->
    let (env, def) = import_let_fun env l typ_vars is_rec cases in
    let e = of_expression env typ_vars e in
    LetFun (l, def, e)
  | Texp_function { cases = [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}] }
  | Texp_function { cases = [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}] } ->
    let x = Name.of_ident x in
    let env = FullEnvi.add_var [] x () env in
    Function (l, x, of_expression env typ_vars e)
  | Texp_function { cases = cases } ->
    let (x, e) = open_cases env typ_vars cases in
    Function (l, x, e)
  | Texp_apply (e_f, e_xs) ->
    let l_f = Loc.of_location e_f.exp_loc in
    (match e_f.exp_desc with
    | Texp_ident (path, _, _)
      when PathName.of_path l_f path = PathName.of_name ["Pervasives"] "raise" ->
      (match e_xs with
      | [(_, Some e_x)] ->
        (match e_x.exp_desc with
        | Texp_construct (x, _, es) ->
          let l_exn = Loc.of_location e_x.exp_loc in
          let x = PathName.of_loc x in
          let x = { x with PathName.base = "raise_" ^ x.PathName.base } in
          let x = Envi.bound_name l_exn x env.FullEnvi.vars in
          let es = List.map (of_expression env typ_vars) es in
          Apply (l, Variable (l_exn, x), [Tuple (Loc.Unknown, es)])
        | _ ->
          Error.raise l "Constructor of an exception expected after a 'raise'.")
      | _ -> Error.raise l "Expected one argument for 'raise'.")
    | Texp_ident (path, _, _)
      when PathName.of_path l_f path = PathName.of_name ["Pervasives"] "!" ->
      (match e_xs with
      | [(_, Some e_x)] ->
        (match e_x.exp_desc with
        | Texp_ident (path, _, _) ->
          let l_x = Loc.of_location e_x.exp_loc in
          let read = PathName.of_path l_x path in
          let read =
            { read with PathName.base = "read_" ^ read.PathName.base } in
          let read = Envi.bound_name l_x read env.FullEnvi.vars in
          Apply (l, Variable (Loc.Unknown, read), [Tuple (Loc.Unknown, [])])
        | _ -> Error.raise l "Name of a reference expected after '!'.")
      | _ -> Error.raise l "Expected one argument for '!'.")
    | Texp_ident (path, _, _)
      when PathName.of_path l_f path = PathName.of_name ["Pervasives"] ":=" ->
      (match e_xs with
      | [(_, Some e_r); (_, Some e_v)] ->
        (match e_r.exp_desc with
        | Texp_ident (path, _, _) ->
          let l_r = Loc.of_location e_r.exp_loc in
          let write = PathName.of_path l_r path in
          let write =
            { write with PathName.base = "write_" ^ write.PathName.base } in
          let write = Envi.bound_name l_r write env.FullEnvi.vars in
          let e_v = of_expression env typ_vars e_v in
          Apply (l, Variable (Loc.Unknown, write), [e_v])
        | _ -> Error.raise l "Name of a reference expected after ':='.")
      | _ -> Error.raise l "Expected two arguments for ':='.")
    | _ ->
      let e_f = of_expression env typ_vars e_f in
      let e_xs = List.map (fun (_, e_x) ->
        match e_x with
        | Some e_x -> of_expression env typ_vars e_x
        | None -> Error.raise l "expected an argument") e_xs in
      Apply (l, e_f, e_xs))
  | Texp_match (e, cases, _, _) ->
    let e = of_expression env typ_vars e in
    let cases = cases |> List.map (fun {c_lhs = p; c_guard = g; c_rhs = e} ->
      if g <> None then Error.warn l "Guard on pattern ignored.";
      let p = Pattern.of_pattern env p in
      let env = Pattern.add_to_env p env in
      (p, of_expression env typ_vars e)) in
    Match (l, e, cases)
  | Texp_tuple es -> Tuple (l, List.map (of_expression env typ_vars) es)
  | Texp_construct (x, _, es) ->
    let x = Envi.bound_name l (PathName.of_loc x) env.FullEnvi.constructors in
    Constructor (l, x, List.map (of_expression env typ_vars) es)
  | Texp_record { fields = fields; extended_expression = None } ->
    Record (l, Array.to_list fields |> List.map (fun (label, definition) ->
      let (x, e) =
        match definition with
        | Kept _ -> Error.raise l "Records with overwriting not handled."
        | Overridden (loc, e) -> (loc, e) in
      let loc = Loc.of_location label.lbl_loc in
      let x = Envi.bound_name loc (PathName.of_loc x) env.FullEnvi.fields in
      (x, of_expression env typ_vars e)))
  | Texp_field (e, x, _) ->
    let x = Envi.bound_name l (PathName.of_loc x) env.FullEnvi.fields in
    Field (l, of_expression env typ_vars e, x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Tuple (Loc.Unknown, [])
      | Some e3 -> of_expression env typ_vars e3 in
    IfThenElse (l, of_expression env typ_vars e1,
      of_expression env typ_vars e2, e3)
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
  | Texp_assert e ->
    let assert_function =
      Envi.bound_name l (PathName.of_name ["OCaml"] "assert") env.FullEnvi.vars in
    Apply (l, Variable (l, assert_function), [of_expression env typ_vars e])
  | _ -> Error.raise l "Expression not handled."

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases (env : unit FullEnvi.t) (typ_vars : Name.t Name.Map.t)
  (cases : case list) : Name.t * Loc.t t =
  let (x, env_vars) = Envi.fresh "x" () env.FullEnvi.vars in
  let env = { env with FullEnvi.vars = env_vars } in
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
    let p = Pattern.of_pattern env p in
    let env = Pattern.add_to_env p env in
    (p, of_expression env typ_vars e)) in
  let bound_x = Envi.bound_name Loc.Unknown (PathName.of_name [] x) env_vars in
  (x, Match (Loc.Unknown, Variable (Loc.Unknown, bound_x), cases))

and import_let_fun (env : unit FullEnvi.t) (loc : Loc.t)
  (typ_vars : Name.t Name.Map.t) (is_rec : Asttypes.rec_flag)
  (cases : value_binding list) : unit FullEnvi.t * Loc.t t Definition.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  let cases = cases |> List.map (fun { vb_pat = p; vb_expr = e } ->
    let loc = Loc.of_location p.pat_loc in
    let p = Pattern.of_pattern env p in
    match p with
    | Pattern.Variable x -> (x, e, loc)
    | _ -> Error.raise loc "A variable name instead of a pattern was expected.") in
  let env_with_let =
    List.fold_left (fun env (x, _, _) -> FullEnvi.add_var [] x () env)
      env cases in
  let env =
    if Recursivity.to_bool is_rec then
      env_with_let
    else
      env in
  let cases = cases |> List.map (fun (x, e, loc) ->
    let (e_typ, typ_vars, new_typ_vars) =
      Type.of_type_expr_new_typ_vars env loc typ_vars e.exp_type in
    let e = of_expression env typ_vars e in
    let (args_names, e_body) = open_function e in
    let (args_typs, e_body_typ) =
      Type.open_type e_typ (List.length args_names) in
    let header = {
      Header.name = x;
      typ_vars = Name.Set.elements new_typ_vars;
      args = List.combine args_names args_typs;
      typ = Some e_body_typ } in
    (header, e_body)) in
  let def = {
    Definition.is_rec = is_rec;
    cases = cases } in
  (env_with_let, def)

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : 'a t) : SmartPrint.t =
  match e with
  | Constant (_, c) -> Constant.to_coq c
  | Variable (_, x) -> BoundName.to_coq x
  | Tuple (_, es) ->
    if es = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (_, x, es) ->
    if es = [] then
      BoundName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space
        (BoundName.to_coq x :: List.map (to_coq true) es)
  | Apply (_, e_f, e_xs) ->
    Pp.parens paren @@ nest @@ (separate space (List.map (to_coq true) (e_f :: e_xs)))
  | Function (_, x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | LetVar (_, x, e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^-^ !^ " :=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | LetFun (_, def, e) ->
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
  | Match (_, e, cases) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline))) ^^
      !^ "end")
  | Record (_, fields) ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
      nest (BoundName.to_coq x ^-^ !^ " :=" ^^ to_coq false e))) ^^ !^ "|}")
  | Field (_, e, x) -> Pp.parens paren @@ nest (BoundName.to_coq x ^^ to_coq true e)
  | IfThenElse (_, e1, e2, e3) ->
    Pp.parens paren @@ nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
