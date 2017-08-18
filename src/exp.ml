(** An expression. *)
open Typedtree
open Types
open SmartPrint

module Header = struct
  type t = {
    name : Name.t;
    typ_vars : Name.t list;
    args : (Name.t * Type.t) list;
    typ : Type.t option }

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
    attribute : Attribute.t;
    cases : (Header.t * 'a) list }

  let pp (pp_a : 'a -> SmartPrint.t) (def : 'a t) : SmartPrint.t =
    OCaml.tuple [Recursivity.pp def.is_rec; Attribute.pp def.attribute;
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
  | Sequence of 'a * 'a t * 'a t (** A sequence of two expressions. *)
  | Return of 'a * 'a t (** Monadic return. *)
  | Bind of 'a * 'a t * Name.t option * 'a t (** Monadic bind. *)
  | Lift of 'a * Effect.Descriptor.t * Effect.Descriptor.t * 'a t
    (** Monadic lift. *)
  | Run of 'a * BoundName.t * Effect.Descriptor.t * 'a t

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
  | Sequence (a, e1, e2) ->
    nest (!^ "Sequence" ^^ OCaml.tuple [pp_a a; pp e1; pp e2])
  | Return (a, e) -> nest (!^ "Return" ^^ OCaml.tuple [pp_a a; pp e])
  | Bind (a, e1, x, e2) -> nest (!^ "Bind" ^^ OCaml.tuple
    [pp_a a; pp e1; nest (OCaml.option Name.pp x); pp e2])
  | Lift (a, d1, d2, e) ->
    nest (!^ "Lift" ^^ OCaml.tuple [
      pp_a a; Effect.Descriptor.pp d1; Effect.Descriptor.pp d2; pp e])
  | Run (a, x, d, e) ->
    nest (!^ "Run" ^^ OCaml.tuple [
      pp_a a; BoundName.pp x; Effect.Descriptor.pp d; pp e])

let annotation (e : 'a t) : 'a =
  match e with
  | Constant (a, _) | Variable (a, _) | Tuple (a, _) | Constructor (a, _, _)
  | Apply (a, _, _) | Function (a, _, _) | LetVar (a, _, _, _)
  | LetFun (a, _, _) | Match (a, _, _) | Record (a, _) | Field (a, _, _)
  | IfThenElse (a, _, _, _) | Sequence (a, _, _) | Return (a, _)
  | Bind (a, _, _, _) | Lift (a, _, _, _) | Run (a, _, _, _) -> a

let rec map (f : 'a -> 'b) (e : 'a t) : 'b t =
  match e with
  | Constant (a, c) -> Constant (f a, c)
  | Variable (a, x) -> Variable (f a, x)
  | Tuple (a, es) -> Tuple (f a, List.map (map f) es)
  | Constructor (a, x, es) -> Constructor (f a, x, List.map (map f) es)
  | Apply (a, e_f, e_xs) -> Apply (f a, map f e_f, List.map (map f) e_xs)
  | Function (a, x, e) -> Function (f a, x, map f e)
  | LetVar (a, x, e1, e2) -> LetVar (f a, x, map f e1, map f e2)
  | LetFun (a, def, e2) ->
    let cases = def.Definition.cases |> List.map (fun (header, e) ->
      (header, map f e)) in
    LetFun (f a, { def with Definition.cases = cases }, map f e2)
  | Match (a, e, cases) ->
    Match (f a, map f e, List.map (fun (p, e) -> (p, map f e)) cases)
  | Record (a, fields) ->
    Record (f a, List.map (fun (x, e) -> (x, map f e)) fields)
  | Field (a, e, x) -> Field (f a, map f e, x)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (f a, map f e1, map f e2, map f e3)
  | Sequence (a, e1, e2) -> Sequence (f a, map f e1, map f e2)
  | Return (a, e) -> Return (f a, map f e)
  | Bind (a, e1, x, e2) -> Bind (f a, map f e1, x, map f e2)
  | Lift (a, d1, d2, e) -> Lift (f a, d1, d2, map f e)
  | Run (a, x, d, e) -> Run (f a, x, d, map f e)

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
  | Texp_function (_, [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}], _)
  | Texp_function (_, [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}], _) ->
    let x = Name.of_ident x in
    let env = FullEnvi.add_var [] x () env in
    Function (l, x, of_expression env typ_vars e)
  | Texp_function (_, cases, _) ->
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
  | Texp_sequence (e1, e2) ->
    Sequence (l, of_expression env typ_vars e1, of_expression env typ_vars e2)
  | Texp_try (e1,
    [{c_lhs = {pat_desc = Tpat_construct (x, _, ps)}; c_rhs = e2}]) ->
    let e1 = of_expression env typ_vars e1 in
    let x = Envi.bound_name l (PathName.of_loc x) env.FullEnvi.descriptors in
    let p = Pattern.Tuple (List.map (Pattern.of_pattern env) ps) in
    Match (l, Run (Loc.Unknown, x, Effect.Descriptor.pure, e1), [
      (let p = Pattern.Constructor (
        Envi.bound_name l (PathName.of_name [] "inl") env.FullEnvi.constructors,
        [Pattern.Variable "x"]) in
      let env = Pattern.add_to_env p env in
      let x = Envi.bound_name l (PathName.of_name [] "x") env.FullEnvi.vars in
      (p, Variable (Loc.Unknown, x)));
      (let p = Pattern.Constructor (
        Envi.bound_name l (PathName.of_name [] "inr") env.FullEnvi.constructors,
        [p]) in
      let env = Pattern.add_to_env p env in
      let e2 = of_expression env typ_vars e2 in
      (p, e2))])
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
  let attrs = cases |> List.map (fun { vb_attributes = attrs; vb_expr = e; vb_pat = p } ->
    let { exp_loc = loc } = e in
    let l = Loc.of_location loc in
    let attr = Attribute.of_attributes l attrs in
    (* The attribute @coq_rec is added if the name finishes by "_coq_rec": *)
    match Pattern.of_pattern env p with
    | Pattern.Variable x ->
      if Str.string_match (Str.regexp ".*_coq_rec$") x 0 then
        Attribute.combine l attr Attribute.CoqRec
      else
        attr
    | _ -> attr (* This branch should not be reached. *)) in
  let attr = List.fold_left (Attribute.combine loc) Attribute.None attrs in
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
    attribute = attr;
    cases = cases } in
  (env_with_let, def)

(** Substitute the name [x] used as a variable (not as a constructor for
    example) in [e] by [e']. *)
let rec substitute (x : Name.t) (e' : 'a t) (e : 'a t) : 'a t =
  match e with
  | Constant _ -> e
  | Variable (_, y) ->
    if PathName.of_name [] x = y.BoundName.path_name then
      e'
    else
      e
  | Tuple (a, es) -> Tuple (a, List.map (substitute x e') es)
  | Constructor (a, y, es) -> Constructor (a, y, List.map (substitute x e') es)
  | Apply (a, e_f, e_xs) ->
    Apply (a, substitute x e' e_f, List.map (substitute x e') e_xs)
  | Function (a, y, e) ->
    if y = x then
      Function (a, y, e)
    else
      Function (a, y, substitute x e' e)
  | LetVar (a, y, e1, e2) ->
    let e1 = substitute x e' e1 in
    let e2 = if x = y then e2 else substitute x e' e2 in
    LetVar (a, y, e1, e2)
  | LetFun (a, def, e2) ->
    let is_x_a_name = List.mem x (Definition.names def) in
    let def =
      if (Recursivity.to_bool def.Definition.is_rec && is_x_a_name) then
        def
      else
        { def with Definition.cases =
          def.Definition.cases |> List.map (fun (header, e1) ->
            if List.exists (fun (y, _) -> y = x) header.Header.args then
              (header, e1)
            else
              (header, substitute x e' e1)) } in
    let e2 = if is_x_a_name then e2 else substitute x e' e2 in
    LetFun (a, def, e2)
  | Match (a, e, cases) ->
    let e = substitute x e' e in
    let cases = cases |> List.map (fun (p, e) ->
      let ys = Pattern.free_variables p in
      if Name.Set.exists (fun y -> y = x) ys then
        (p, e)
      else
        (p, substitute x e' e)) in
    Match (a, e, cases)
  | Record (a, fields) ->
    Record (a, List.map (fun (y, e) -> (y, substitute x e' e)) fields)
  | Field (a, e, y) -> Field (a, substitute x e' e, y)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (a, substitute x e' e1, substitute x e' e2, substitute x e' e3)
  | Sequence (a, e1, e2) ->
    Sequence (a, substitute x e' e1, substitute x e' e2)
  | Run (a, y, n, e) -> Run (a, y, n, substitute x e' e)
  | Return (a, e) -> Return (a, substitute x e' e)
  | Bind (a, e1, y, e2) ->
    let e1 = substitute x e' e1 in
    let e2 =
      match y with
      | None -> substitute x e' e2
      | Some y ->
        if y = x then
          e2
        else
          substitute x e' e2 in
    Bind (a, e1, y, e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, substitute x e' e)

let rec monadise_let_rec (env : unit FullEnvi.t) (e : Loc.t t) : Loc.t t =
  match e with
  | Constant _ | Variable _ -> e
  | Tuple (a, es) ->
    Tuple (a, List.map (monadise_let_rec env) es)
  | Constructor (a, x, es) ->
    Constructor (a, x, List.map (monadise_let_rec env) es)
  | Apply (a, e_f, e_xs) ->
    Apply (a, monadise_let_rec env e_f, List.map (monadise_let_rec env) e_xs)
  | Function (a, x, e) ->
    let env = FullEnvi.add_var [] x () env in
    Function (a, x, monadise_let_rec env e)
  | LetVar (a, x, e1, e2) ->
    let e1 = monadise_let_rec env e1 in
    let env = FullEnvi.add_var [] x () env in
    let e2 = monadise_let_rec env e2 in
    LetVar (a, x, e1, e2)
  | LetFun (a, def, e2) ->
    let (env, defs) = monadise_let_rec_definition env def in
    let e2 = monadise_let_rec env e2 in
    List.fold_right (fun def e2 -> LetFun (a, def, e2)) defs e2
  | Match (a, e, cases) ->
    Match (a, monadise_let_rec env e,
      cases |> List.map (fun (p, e) ->
        let env = Pattern.add_to_env p env in
        (p, monadise_let_rec env e)))
  | Record (a, fields) ->
    Record (a, fields |> List.map (fun (x, e) -> (x, monadise_let_rec env e)))
  | Field (a, e, x) -> Field (a, monadise_let_rec env e, x)
  | IfThenElse (a, e1, e2, e3) ->
    IfThenElse (a, monadise_let_rec env e1,
      monadise_let_rec env e2,
      monadise_let_rec env e3)
  | Sequence (a, e1, e2) ->
    Sequence (a, monadise_let_rec env e1,
      monadise_let_rec env e2)
  | Run (a, x, d, e) -> Run (a, x, d, monadise_let_rec env e)
  | Return (a, e) -> monadise_let_rec env e
  | Bind (a, e1, x, e2) ->
    let e1 = monadise_let_rec env e1 in
    let env = match x with
      | None -> env
      | Some x -> FullEnvi.add_var [] x () env in
    Bind (a, e1, x, monadise_let_rec env e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, monadise_let_rec env e)

and monadise_let_rec_definition (env : unit FullEnvi.t)
  (def : Loc.t t Definition.t) : unit FullEnvi.t * Loc.t t Definition.t list =
  if Recursivity.to_bool def.Definition.is_rec &&
    def.Definition.attribute <> Attribute.CoqRec then
    let var (x : Name.t) env : Loc.t t =
      Variable (Loc.Unknown,
        Envi.bound_name Loc.Unknown (PathName.of_name [] x) env.FullEnvi.vars) in
    let env_in_def = Definition.env_in_def def env in
    (* Add the suffix "_rec" to the names. *)
    let def' = { def with Definition.cases =
      def.Definition.cases |> List.map (fun (header, e) ->
        let (name_rec, _) = Envi.fresh (header.Header.name ^ "_rec") ()
          env_in_def.FullEnvi.vars in
        ({ header with Header.name = name_rec }, e)) } in
    let env_after_def' = Definition.env_in_def def' env in
    (* Add the argument "counter" and monadise the bodies. *)
    let def' = { def' with Definition.cases =
      def'.Definition.cases |> List.map (fun (header, e) ->
        let name_rec = header.Header.name in
        let (counter, _) =
          Envi.fresh "counter" () env_after_def'.FullEnvi.vars in
        let args_rec =
          (counter,
            Type.Apply (Envi.bound_name Loc.Unknown (PathName.of_name [] "nat")
              env_after_def'.FullEnvi.typs,
            [])) :: header.Header.args in
        let header_rec =
          { header with Header.name = name_rec; args = args_rec } in
        let env_in_name_rec =
          Header.env_in_header header_rec env_after_def' () in
        let e_name_rec = monadise_let_rec env_in_name_rec e in
        (header_rec, e_name_rec)) } in
    (* Do the substitutions. *)
    let def' = { def' with Definition.cases = List.map2 (fun name (header, e) ->
      let counter = fst (List.hd header.Header.args) in
      let env = Header.env_in_header header env_after_def' () in
      let e_name_rec =
        List.fold_left2 (fun e_name_rec name (header, e) ->
          substitute name
            (Apply (Loc.Unknown, var header.Header.name env,
              [var counter env])) e_name_rec)
          e (Definition.names def) def'.Definition.cases in
      let e_name_rec = Match (Loc.Unknown, var counter env, [
        (Pattern.Constructor (Envi.bound_name Loc.Unknown (PathName.of_name [] "O")
          env.FullEnvi.constructors, []),
          Apply (Loc.Unknown, var "not_terminated" env,
            [Tuple (Loc.Unknown, [])]));
        (Pattern.Constructor (
          Envi.bound_name Loc.Unknown (PathName.of_name [] "S") env.FullEnvi.constructors,
          [Pattern.Variable counter]),
          e_name_rec)]) in
      (header, e_name_rec))
      (Definition.names def) def'.Definition.cases } in
    (* Add the definitions without the "_rec" suffix. *)
    let defs = List.map2 (fun name_rec (header, _) ->
      let env = Header.env_in_header header env_after_def' () in
      let e = Apply (Loc.Unknown,
        var name_rec env,
        Apply (Loc.Unknown, var "read_counter" env,
          [Tuple (Loc.Unknown, [])]) ::
            List.map (fun (x, _) -> var x env) header.Header.args) in
      { Definition.is_rec = Recursivity.New false;
        attribute = Attribute.None;
        cases = [header, e] })
      (Definition.names def') def.Definition.cases in
    let env =
      List.fold_left (fun env def -> Definition.env_after_def def env)
        env defs in
    (env, def' :: defs)
  else
    let def = { def with
      Definition.cases = def.Definition.cases |> List.map (fun (header, e) ->
        (header, monadise_let_rec (Header.env_in_header header env ()) e)) } in
    let env = Definition.env_after_def def env in
    (env, [def])

let rec effects (env : Effect.Type.t FullEnvi.t) (e : Loc.t t)
  : (Loc.t * Effect.t) t =
  let compound (es : Loc.t t list) : (Loc.t * Effect.t) t list * Effect.t =
    let es = List.map (effects env) es in
    let descriptor = Effect.Descriptor.union (es |> List.map (fun e ->
      let (loc, effect) = annotation e in
      if not (Effect.Type.is_pure effect.Effect.typ) then
        Error.warn loc "Compounds cannot have functional effects; effect ignored.";
      effect.Effect.descriptor)) in
    (es, { Effect.descriptor = descriptor; typ = Effect.Type.Pure }) in
  match e with
  | Constant (l, c) -> Constant ((l, Effect.pure), c)
  | Variable (l, x) ->
    (try
      let effect =
        { Effect.descriptor = Effect.Descriptor.pure;
          typ = Envi.find x env.FullEnvi.vars Effect.Type.depth_lift } in
      Variable ((l, effect), x)
    with Not_found ->
      let message = BoundName.pp x ^^ !^ "not found: supposed to be pure." in
      Error.warn l (SmartPrint.to_string 80 2 message);
      Variable ((l, {
        Effect.descriptor = Effect.Descriptor.pure;
        typ = Effect.Type.Pure }), x))
  | Tuple (l, es) ->
    let (es, effect) = compound es in
    Tuple ((l, effect), es)
  | Constructor (l, x, es) ->
    let (es, effect) = compound es in
    Constructor ((l, effect), x, es)
  | Apply (l, e_f, e_xs) ->
    let e_f = effects env e_f in
    let effect_e_f = snd (annotation e_f) in
    let e_xs = List.map (effects env) e_xs in
    let effects_e_xs = List.map (fun e_x -> snd (annotation e_x)) e_xs in
    if effects_e_xs |> List.for_all (fun effect_e_x ->
      Effect.Type.is_pure effect_e_x.Effect.typ) then
      let rec e_xss typ e_xs : ('b t list * Effect.Descriptor.t) list =
        match e_xs with
        | [] -> []
        | e_x :: e_xs ->
          let e_xss = e_xss (Effect.Type.return_type typ 1) e_xs in
          let d = Effect.Type.return_descriptor typ 1 in
          if Effect.Descriptor.is_pure d then
            match e_xss with
            | [] -> [([e_x], Effect.Descriptor.pure)]
            | (e_xs', d') :: e_xss -> ((e_x :: e_xs'), d') :: e_xss
          else
            ([e_x], d) :: e_xss in
      let e_xss = e_xss effect_e_f.Effect.typ e_xs in
      List.fold_left (fun e (e_xs, d) ->
        let effect_e = snd (annotation e) in
        let effects_e_xs = List.map (fun e_x -> snd (annotation e_x)) e_xs in
        let descriptor = Effect.Descriptor.union (
          effect_e.Effect.descriptor ::
          Effect.Type.return_descriptor effect_e.Effect.typ (List.length e_xs) ::
          List.map (fun effect_e_x -> effect_e_x.Effect.descriptor) effects_e_xs) in
        let typ = Effect.Type.return_type effect_e.Effect.typ (List.length e_xs) in
        let effect = { Effect.descriptor = descriptor; typ = typ } in
        Apply ((l, effect), e, e_xs))
        e_f e_xss
    else
      Error.raise l "Function arguments cannot have functional effects."
  | Function (l, x, e) ->
    let env = FullEnvi.add_var [] x Effect.Type.Pure env in
    let e = effects env e in
    let effect_e = snd (annotation e) in
    let effect = {
      Effect.descriptor = Effect.Descriptor.pure;
      typ = Effect.Type.Arrow (
        effect_e.Effect.descriptor, effect_e.Effect.typ) } in
    Function ((l, effect), x, e)
  | LetVar (l, x, e1, e2) ->
    let e1 = effects env e1 in
    let effect1 = snd (annotation e1) in
    let env = FullEnvi.add_var [] x effect1.Effect.typ env in
    let e2 = effects env e2 in
    let effect2 = snd (annotation e2) in
    let descriptor = Effect.Descriptor.union [
      effect1.Effect.descriptor; effect2.Effect.descriptor] in
    let effect = {
      Effect.descriptor = descriptor;
      typ = effect2.Effect.typ } in
    LetVar ((l, effect), x, e1, e2)
  | LetFun (l, def, e2) ->
    let def = effects_of_def env def in
    let env = env_after_def_with_effects env def in
    let e2 = effects env e2 in
    let effect2 = snd (annotation e2) in
    LetFun ((l, effect2), def, e2)
  | Match (l, e, cases) ->
    let e = effects env e in
    let effect_e = snd (annotation e) in
    if Effect.Type.is_pure effect_e.Effect.typ then
      let cases = cases |> List.map (fun (p, e) ->
        let pattern_vars = Pattern.free_variables p in
        let env = Name.Set.fold (fun x env ->
          FullEnvi.add_var [] x Effect.Type.Pure env)
          pattern_vars env in
        (p, effects env e)) in
      let effect = Effect.union (cases |> List.map (fun (_, e) ->
        snd (annotation e))) in
      let effect = {
        Effect.descriptor = Effect.Descriptor.union
          [effect_e.Effect.descriptor; effect.Effect.descriptor];
        typ = effect.Effect.typ } in
      Match ((l, effect), e, cases)
    else
      Error.raise l "Cannot match a value with functional effects."
  | Record (l, fields) ->
    let (es, effect) = compound (List.map snd fields) in
    Record ((l, effect), List.map2 (fun (x, _) e -> (x, e)) fields es)
  | Field (l, e, x) ->
    let e = effects env e in
    let effect = snd (annotation e) in
    if Effect.Type.is_pure effect.Effect.typ then
      Field ((l, effect), e, x)
    else
      Error.raise l "Cannot take a field of a value with functional effects."
  | IfThenElse (l, e1, e2, e3) ->
    let e1 = effects env e1 in
    let effect_e1 = snd (annotation e1) in
    if Effect.Type.is_pure effect_e1.Effect.typ then
      let e2 = effects env e2 in
      let e3 = effects env e3 in
      let effect = Effect.union ([e2; e3] |> List.map (fun e ->
        snd (annotation e))) in
      let effect = {
        Effect.descriptor = Effect.Descriptor.union
          [effect_e1.Effect.descriptor; effect.Effect.descriptor];
        typ = effect.Effect.typ } in
      IfThenElse ((l, effect), e1, e2, e3)
    else
      Error.raise l "Cannot do an if on a value with functional effects."
  | Sequence (l, e1, e2) ->
    let e1 = effects env e1 in
    let effect_e1 = snd (annotation e1) in
    let e2 = effects env e2 in
    let effect_e2 = snd (annotation e2) in
    let effect = {
      Effect.descriptor = Effect.Descriptor.union
        [effect_e1.Effect.descriptor; effect_e2.Effect.descriptor];
      typ = effect_e2.Effect.typ } in
    Sequence ((l, effect), e1, e2)
  | Run (l, x, d, e) ->
    let e = effects env e in
    let effect_e = snd (annotation e) in
    let effect = { effect_e with Effect.descriptor =
      Effect.Descriptor.remove x effect_e.Effect.descriptor } in
    Run ((l, effect), x, d, e)
  | Return _ | Bind _ | Lift _ ->
    Error.raise Loc.Unknown
      "Cannot compute effects on an explicit return, bind or lift."

and env_after_def_with_effects (env : Effect.Type.t FullEnvi.t)
  (def : (Loc.t * Effect.t) t Definition.t) : Effect.Type.t FullEnvi.t =
  List.fold_left (fun env (header, e) ->
    let effect = snd (annotation e) in
    let effect_typ = Effect.function_typ header.Header.args effect in
    FullEnvi.add_var [] header.Header.name effect_typ env)
    env def.Definition.cases

and effects_of_def_step (env : Effect.Type.t FullEnvi.t)
  (def : Loc.t t Definition.t) : (Loc.t * Effect.t) t Definition.t =
  { def with Definition.cases =
    def.Definition.cases |> List.map (fun (header, e) ->
      let env = Header.env_in_header header env Effect.Type.Pure in
      (header, effects env e)) }

and effects_of_def (env : Effect.Type.t FullEnvi.t) (def : Loc.t t Definition.t)
  : (Loc.t * Effect.t) t Definition.t =
  let rec fix_effect (def' : (Loc.t * Effect.t) t Definition.t) =
    let env =
      if Recursivity.to_bool def.Definition.is_rec then
        env_after_def_with_effects env def'
      else
        env in
    let def'' = effects_of_def_step env def in
    if def' = def'' then
      def'
    else
      fix_effect def'' in
  let env =
    if Recursivity.to_bool def.Definition.is_rec then
      List.fold_left (fun env (header, _) ->
        FullEnvi.add_var [] header.Header.name Effect.Type.Pure env)
        env def.Definition.cases
    else
      env in
  fix_effect (effects_of_def_step env def)

let rec monadise (env : unit FullEnvi.t) (e : (Loc.t * Effect.t) t) : Loc.t t =
  let descriptor e = (snd (annotation e)).Effect.descriptor in
  let lift d1 d2 e =
    if Effect.Descriptor.eq d1 d2 then
      e
    else if Effect.Descriptor.is_pure d1 then
      Return (Loc.Unknown, e)
    else
      Lift (Loc.Unknown, d1, d2, e) in
  (** [d1] is the descriptor of [e1], [d2] of [e2]. *)
  let bind d1 d2 d e1 x e2 =
    if Effect.Descriptor.is_pure d1 then
      match x with
      | Some x -> LetVar (Loc.Unknown, x, e1, e2)
      | None -> e2
    else
      Bind (Loc.Unknown, lift d1 d e1, x, lift d2 d e2) in
  (** [k es'] is supposed to raise the effect [d]. *)
  let rec monadise_list env es d es' k =
    match es with
    | [] -> k (List.rev es')
    | e :: es ->
      let d_e = descriptor e in
      if Effect.Descriptor.is_pure d_e then
        monadise_list env es d (map fst e :: es') k
      else
        let e' = monadise env e in
        let (x, env_vars) = Envi.fresh "x" () env.FullEnvi.vars in
        let env = { env with FullEnvi.vars = env_vars } in
        bind d_e d d e' (Some x) (monadise_list env es d
          (Variable (Loc.Unknown,
            Envi.bound_name Loc.Unknown (PathName.of_name [] x) env.FullEnvi.vars) :: es') k) in
  let d = descriptor e in
  match e with
  | Constant ((l, _), c) -> Constant (l, c)
  | Variable ((l, _), x) -> Variable (l, x)
  | Tuple ((l, _), es) ->
    monadise_list env es d [] (fun es' ->
      lift Effect.Descriptor.pure d (Tuple (l, es')))
  | Constructor ((l, _), x, es) ->
    monadise_list env es d [] (fun es' ->
      lift Effect.Descriptor.pure d (Constructor (l, x, es')))
  | Apply ((l, _), e_f, e_xs) ->
    let effect_f = (snd (annotation e_f)).Effect.typ in
    monadise_list env (e_f :: e_xs) d [] (fun es' ->
      match es' with
      | e_f :: e_xs ->
        let return_descriptor =
          Effect.Type.return_descriptor effect_f (List.length e_xs) in
        lift return_descriptor d (Apply (l, e_f, e_xs))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Function ((l, _), x, e) ->
    let env = FullEnvi.add_var [] x () env in
    Function (l, x, monadise env e)
  | LetVar ((l, _), x, e1, e2) -> (* TODO: use l *)
    let (d1, d2) = (descriptor e1, descriptor e2) in
    let e1 = monadise env e1 in
    let env = FullEnvi.add_var [] x () env in
    let e2 = monadise env e2 in
    bind d1 d2 d e1 (Some x) e2
  | LetFun ((l, _), def, e2) ->
    let env_in_def = Definition.env_in_def def env in
    let def = { def with
      Definition.cases = def.Definition.cases |> List.map (fun (header, e) ->
        let typ = match header.Header.typ with
        | Some typ -> Some (Type.monadise typ (snd (annotation e)))
        | None -> None in
      let header = { header with Header.typ = typ } in
      let env = Header.env_in_header header env_in_def () in
      let e = monadise env e in
      (header, e)) } in
    let env = Definition.env_after_def def env in
    let e2 = monadise env e2 in
    LetFun (l, def, e2)
  | Match ((l, _), e, cases) ->
    monadise_list env [e] d [] (fun es' ->
      match es' with
      | [e] ->
        let cases = cases |> List.map (fun (p, e)->
          let env = Name.Set.fold (fun x env -> FullEnvi.add_var [] x () env)
            (Pattern.free_variables p) env in
          (p, lift (descriptor e) d (monadise env e))) in
        Match (l, e, cases)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Record ((l, _), fields) ->
    monadise_list env (List.map snd fields) d [] (fun es' ->
      let fields = List.map2 (fun (f, _) e -> (f, e)) fields es' in
      lift Effect.Descriptor.pure d (Record (l, fields)))
  | Field ((l, _), e, x) ->
    monadise_list env [e] d [] (fun es' ->
      match es' with
      | [e] -> lift Effect.Descriptor.pure d (Field (l, e, x))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | IfThenElse ((l, _), e1, e2, e3) ->
    let (d2, d3) = (descriptor e2, descriptor e3) in
    monadise_list env [e1] d [] (fun es' ->
      match es' with
      | [e1] ->
        let e2 = lift d2 d (monadise env e2) in
        let e3 = lift d3 d (monadise env e3) in
        IfThenElse (l, e1, e2, e3)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Sequence ((l, _), e1, e2) -> (* TODO: use l *)
    let (d1, d2) = (descriptor e1, descriptor e2) in
    let e1 = monadise env e1 in
    let e2 = monadise env e2 in
    bind d1 d2 d e1 None e2
  | Run ((l, _), x, _, e) ->
    Run (l, x, descriptor e, monadise env e)
  | Return _ | Bind _ | Lift _ ->
    failwith "Unexpected arguments for 'monadise'."

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
  | Sequence (_, e1, e2) ->
    nest (to_coq true e1 ^-^ !^ ";" ^^ newline ^^ to_coq false e2)
  | Run (_, x, d, e) ->
    let n = Effect.Descriptor.index x d in
    let output = nest (!^ "Exception.run" ^^ OCaml.int n ^^ to_coq true e ^^ !^ "tt") in
    Pp.parens paren output
  | Return (_, e) -> Pp.parens paren @@ nest (!^ "ret" ^^ to_coq true e)
  | Bind (_, e1, x, e2) ->
    Pp.parens paren @@ nest (
      !^ "let!" ^^ (match x with
        | None -> !^ "_"
        | Some x -> Name.to_coq x) ^-^ !^ " :=" ^^
        to_coq false e1 ^^ !^ "in" ^^ newline ^^
      to_coq false e2)
  | Lift (_, d1, d2, e) ->
    Pp.parens paren @@ nest (
      !^ "lift" ^^ Effect.Descriptor.subset_to_coq d1 d2 ^^ to_coq true e)
