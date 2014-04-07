(** An expression. *)
open Typedtree
open Types
open SmartPrint

module Header = struct
  (** TODO: update comment.
    A "let" of a function: the recursivity flag, the function name, the type variables,
    the names and types of the arguments, the return type, the body and the expression
    in which we do the "let". We need to group [Let] and [Function] in one constructor
    to make the Coq's fixpoint operator work (and have a nicer pretty-printing). *)
  type t =
    Recursivity.t * Attribute.t * Name.t * Name.t list * (Name.t * Type.t) list * Type.t option

  let pp (header : t) : SmartPrint.t =
    let (is_rec, attr, x, typ_vars, args, typ) = header in
    OCaml.tuple [
      Attribute.pp attr; Recursivity.pp is_rec; Name.pp x;
      OCaml.list Name.pp typ_vars;
      OCaml.list (fun (x, typ) -> OCaml.tuple [Name.pp x; Type.pp typ]) args;
      OCaml.option Type.pp typ]

  let variable (x : Name.t) : t =
    (Recursivity.New false, Attribute.None, x, [], [], None)

  let env_in_header (header : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    let (is_rec, _, x, _, args, _) = header in
    let env_vars =
      if Recursivity.to_bool is_rec then
        Envi.add_name x () env.FullEnvi.vars
      else
        env.FullEnvi.vars in
    let env_vars =
      List.fold_left (fun env_vars (y, _) -> Envi.add_name y () env_vars)
        env_vars args in
    { env with FullEnvi.vars = env_vars }
end

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type 'a t =
  | Constant of 'a * Constant.t
  | Variable of 'a * BoundName.t
  | Tuple of 'a * 'a t list (** A tuple of expressions. *)
  | Constructor of 'a * BoundName.t * 'a t list (** A constructor name and a list of arguments. *)
  | Apply of 'a * 'a t * 'a t list (** An application. *)
  | Function of 'a * Name.t * 'a t (** An argument name and a body. *)
  | Let of 'a * Header.t * 'a t * 'a t
  | Match of 'a * 'a t * (Pattern.t * 'a t) list (** Match an expression to a list of patterns. *)
  | Record of 'a * (BoundName.t * 'a t) list (** Construct a record giving an expression for each field. *)
  | Field of 'a * 'a t * BoundName.t (** Access to a field of a record. *)
  | IfThenElse of 'a * 'a t * 'a t * 'a t (** The "else" part may be unit. *)
  | Sequence of 'a * 'a t * 'a t (** A sequence of two expressions. *)
  | Return of 'a * 'a t (** Monadic return. *)
  | Bind of 'a * 'a t * Name.t option * 'a t (** Monadic bind. *)
  | Lift of 'a * Effect.Descriptor.t * Effect.Descriptor.t * 'a t (** Monadic lift. *)
  | Run of 'a * BoundName.t * Effect.Descriptor.t * 'a t

let annotation (e : 'a t) : 'a =
  match e with
  | Constant (a, _) | Variable (a, _) | Tuple (a, _) | Constructor (a, _, _)
    | Apply (a, _, _) | Function (a, _, _) | Let (a, _, _, _) | Match (a, _, _)
    | Record (a, _) | Field (a, _, _) | IfThenElse (a, _, _, _)
    | Sequence (a, _, _) | Return (a, _) | Bind (a, _, _, _) | Lift (a, _, _, _)
    | Run (a, _, _, _) -> a

let rec map (f : 'a -> 'b) (e : 'a t) : 'b t =
  match e with
  | Constant (a, c) -> Constant (f a, c)
  | Variable (a, x) -> Variable (f a, x)
  | Tuple (a, es) -> Tuple (f a, List.map (map f) es)
  | Constructor (a, x, es) -> Constructor (f a, x, List.map (map f) es)
  | Apply (a, e_f, e_xs) -> Apply (f a, map f e_f, List.map (map f) e_xs)
  | Function (a, x, e) -> Function (f a, x, map f e)
  | Let (a, header, e1, e2) -> Let (f a, header, map f e1, map f e2)
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

let rec pp (pp_a : 'a -> SmartPrint.t) (e : 'a t) : SmartPrint.t =
  let pp = pp pp_a in
  match e with
  | Constant (a, c) -> nest (!^ "Constant" ^^ OCaml.tuple [pp_a a; Constant.pp c])
  | Variable (a, x) -> nest (!^ "Variable" ^^ OCaml.tuple [pp_a a; BoundName.pp x])
  | Tuple (a, es) ->
    nest (!^ "Tuple" ^^ OCaml.tuple (pp_a a :: List.map pp es))
  | Constructor (a, x, es) ->
    nest (!^ "Constructor" ^^ OCaml.tuple (pp_a a :: BoundName.pp x :: List.map pp es))
  | Apply (a, e_f, e_xs) ->
    nest (!^ "Apply" ^^ OCaml.tuple [pp_a a; pp e_f; OCaml.list pp e_xs])
  | Function (a, x, e) ->
    nest (!^ "Function" ^^ OCaml.tuple [pp_a a; Name.pp x; pp e])
  | Let (a, header, e1, e2) ->
    nest (!^ "Let" ^^ pp_a a ^^ Header.pp header ^^ !^ "=" ^^ newline ^^
      indent (pp e1) ^^ !^ "in" ^^ newline ^^
      pp e2)
  | Match (a, e, cases) ->
    nest (!^ "Match" ^^ OCaml.tuple [pp_a a; pp e;
      cases |> OCaml.list (fun (p, e) ->
        nest @@ parens (Pattern.pp p ^-^ !^ "," ^^ pp e))])
  | Record (a, fields) ->
    nest (!^ "Record" ^^ OCaml.tuple (pp_a a :: (fields |> List.map (fun (x, e) ->
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
    nest (!^ "Lift" ^^
      OCaml.tuple [pp_a a; Effect.Descriptor.pp d1; Effect.Descriptor.pp d2; pp e])
  | Run (a, x, d, e) ->
    nest (!^ "Run" ^^ OCaml.tuple [pp_a a; BoundName.pp x; Effect.Descriptor.pp d; pp e])

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : 'a t) : Name.t list * 'a t =
  match e with
  | Function (_, x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (env : unit FullEnvi.t) (e : expression) : Loc.t t =
  let l = Loc.of_location e.exp_loc in
  match e.exp_desc with
  | Texp_ident (path, _, _) ->
    let x = Envi.bound_name (PathName.of_path path) env.FullEnvi.vars in
    Variable (l, x)
  | Texp_constant constant -> Constant (l, Constant.of_constant constant)
  | Texp_let (rec_flag, [{ vb_pat = pattern; vb_expr = e1; vb_attributes = attrs }], e2) ->
    let (env, rec_flag, pattern, free_typ_vars, args, body_typ, body) =
      import_let_fun env rec_flag pattern e1 in
    let attr = Attribute.of_attributes attrs in
    let e2 = of_expression env e2 in
    (match (pattern, args) with
    | (Pattern.Variable name, []) ->
      Let (l, (Recursivity.New false, attr, name, [], [], None), body, e2)
    | (_, []) -> Match (l, body, [pattern, e2])
    | (Pattern.Variable name, _) ->
      Let (l, (rec_flag, attr, name, free_typ_vars, args, Some body_typ), body, e2)
    | _ -> Error.raise l "Cannot match a function definition on a pattern.")
  | Texp_function (_, [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}], _)
  | Texp_function (_, [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}], _) ->
    let x = Name.of_ident x in
    let env = { env with FullEnvi.vars = Envi.add_name x () env.FullEnvi.vars } in
    Function (l, x, of_expression env e)
  | Texp_function (_, cases, _) ->
    let (x, e) = open_cases env cases in
    Function (l, x, e)
  | Texp_apply (e_f, e_xs) ->
    (match e_f.exp_desc with
    | Texp_ident (path, _, _)
      when PathName.of_path path = PathName.of_name ["Pervasives"] "raise" ->
      (match e_xs with
      | [(_, Some e_x, _)] ->
        (match e_x.exp_desc with
        | Texp_construct (x, _, es) ->
          let l_exn = Loc.of_location e_x.exp_loc in
          let x = PathName.of_loc x in
          let x = { x with PathName.base = "raise_" ^ x.PathName.base } in
          let x = Envi.bound_name x env.FullEnvi.vars in
          let es = List.map (of_expression env) es in
          Apply (l, Variable (l_exn, x), [Tuple (Loc.Unknown, es)])
        | _ -> Error.raise l "Constructor of an exception expected after a 'raise'.")
      | _ -> Error.raise l "Expected one argument for 'raise'.")
    | Texp_ident (path, _, _)
      when PathName.of_path path = PathName.of_name ["Pervasives"] "!" ->
      (match e_xs with
      | [(_, Some e_x, _)] ->
        (match e_x.exp_desc with
        | Texp_ident (path, _, _) ->
          let read = PathName.of_path path in
          let read = { read with PathName.base = "read_" ^ read.PathName.base } in
          let read = Envi.bound_name read env.FullEnvi.vars in
          Apply (l, Variable (Loc.Unknown, read), [Tuple (Loc.Unknown, [])])
        | _ -> Error.raise l "Name of a reference expected after '!'.")
      | _ -> Error.raise l "Expected one argument for '!'.")
    | Texp_ident (path, _, _)
      when PathName.of_path path = PathName.of_name ["Pervasives"] ":=" ->
      (match e_xs with
      | [(_, Some e_r, _); (_, Some e_v, _)] ->
        (match e_r.exp_desc with
        | Texp_ident (path, _, _) ->
          let write = PathName.of_path path in
          let write = { write with PathName.base = "write_" ^ write.PathName.base } in
          let write = Envi.bound_name write env.FullEnvi.vars in
          let e_v = of_expression env e_v in
          Apply (l, Variable (Loc.Unknown, write), [e_v])
        | _ -> Error.raise l "Name of a reference expected after ':='.")
      | _ -> Error.raise l "Expected two arguments for ':='.")
    | _ ->
      let e_f = of_expression env e_f in
      let e_xs = List.map (fun (_, e_x, _) ->
        match e_x with
        | Some e_x -> of_expression env e_x
        | None -> Error.raise l "expected an argument") e_xs in
      Apply (l, e_f, e_xs))
  | Texp_match (e, cases, _) ->
    let e = of_expression env e in
    let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
      let p = Pattern.of_pattern env p in
      let env = Pattern.add_to_env p env in
      (p, of_expression env e)) in
    Match (l, e, cases)
  | Texp_tuple es -> Tuple (l, List.map (of_expression env) es)
  | Texp_construct (x, _, es) ->
    let x = Envi.bound_name (PathName.of_loc x) env.FullEnvi.constructors in
    Constructor (l, x, List.map (of_expression env) es)
  | Texp_record (fields, _) ->
    Record (l, fields |> List.map (fun (x, _, e) ->
      let x = Envi.bound_name (PathName.of_loc x) env.FullEnvi.fields in
      (x, of_expression env e)))
  | Texp_field (e, x, _) ->
    let x = Envi.bound_name (PathName.of_loc x) env.FullEnvi.fields in
    Field (l, of_expression env e, x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Tuple (Loc.Unknown, [])
      | Some e3 -> of_expression env e3 in
    IfThenElse (l, of_expression env e1,
      of_expression env e2, e3)
  | Texp_sequence (e1, e2) ->
    Sequence (l, of_expression env e1, of_expression env e2)
  | Texp_try (e1, [{c_lhs = {pat_desc = Tpat_construct (x, _, ps)}; c_rhs = e2}]) ->
    let e1 = of_expression env e1 in
    let x = Envi.bound_name (PathName.of_loc x) env.FullEnvi.descriptors in
    let p = Pattern.Tuple (List.map (Pattern.of_pattern env) ps) in
    Match (l, Run (Loc.Unknown, x, Effect.Descriptor.pure, e1), [
      (let p = Pattern.Constructor (
        Envi.bound_name (PathName.of_name [] "inl") env.FullEnvi.constructors,
        [Pattern.Variable "x"]) in
      let env = Pattern.add_to_env p env in
      let x = Envi.bound_name (PathName.of_name [] "x") env.FullEnvi.vars in
      (p, Variable (Loc.Unknown, x)));
      (let p = Pattern.Constructor (
        Envi.bound_name (PathName.of_name [] "inr") env.FullEnvi.constructors,
        [p]) in
      let env = Pattern.add_to_env p env in
      let e2 = of_expression env e2 in
      (p, e2))])
  | Texp_setfield _ -> Error.raise l "Set field not handled."
  | Texp_array _ -> Error.raise l "Arrays not handled."
  | Texp_while _ -> Error.raise l "While loops not handled."
  | Texp_for _ -> Error.raise l "For loops not handled."
  | Texp_assert _ -> Error.raise l "Assertions not handled."
  | _ -> Error.raise l "Expression not handled."

(** Generate a variable and a "match" on this variable from a list of patterns. *)
and open_cases (env : unit FullEnvi.t) (cases : case list)
  : Name.t * Loc.t t =
  let (x, env_vars) = Envi.fresh "x" () env.FullEnvi.vars in
  let env = { env with FullEnvi.vars = env_vars } in
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
    let p = Pattern.of_pattern env p in
    let env = Pattern.add_to_env p env in
    (p, of_expression env e)) in
  let bound_x = Envi.bound_name (PathName.of_name [] x) env_vars in
  (x, Match (Loc.Unknown, Variable (Loc.Unknown, bound_x), cases))

and import_let_fun (env : unit FullEnvi.t) (rec_flag : Asttypes.rec_flag)
  (pattern : pattern) (e : expression)
  : unit FullEnvi.t * Recursivity.t * Pattern.t * Name.t list *
    (Name.t * Type.t) list * Type.t * Loc.t t =
  let pattern = Pattern.of_pattern env pattern in
  let is_rec = Recursivity.of_rec_flag rec_flag in
  let env_with_let =
    Pattern.add_to_env pattern env in
  let env =
    if Recursivity.to_bool is_rec then
      env_with_let
    else
      env in
  let e_schema = Schema.of_type (Type.of_type_expr env.FullEnvi.typs e.exp_type) in
  let e = of_expression env e in
  let (args_names, e_body) = open_function e in
  let e_typ = e_schema.Schema.typ in
  let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
  (env_with_let, is_rec, pattern, e_schema.Schema.variables,
    List.combine args_names args_typs, e_body_typ, e_body)

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
  | Let (a, (is_rec, attr, y, typ_args, args, typ), e1, e2) ->
    let e1 =
      if (Recursivity.to_bool is_rec && y = x)
        || List.exists (fun (y, _) -> y = x) args then
        e1
      else
        substitute x e' e1 in
    let e2 =
      if y = x then
        e2
      else
        substitute x e' e2 in
    Let (a, (is_rec, attr, y, typ_args, args, typ), e1, e2)
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
    let env = { env with FullEnvi.vars = Envi.add_name x () env.FullEnvi.vars } in
    Function (a, x, monadise_let_rec env e)
  | Let (a, header, e1, e2) ->
    let (env, defs) = monadise_let_rec_definition env header e1 in
    let e2 = monadise_let_rec env e2 in
    List.fold_right (fun (header, e) e2 -> Let (a, header, e, e2)) defs e2
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
      | Some x ->
        { env with FullEnvi.vars = Envi.add_name x () env.FullEnvi.vars } in
    Bind (a, e1, x, monadise_let_rec env e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, monadise_let_rec env e)

and monadise_let_rec_definition (env : unit FullEnvi.t)
  (header : Header.t) (e : Loc.t t)
  : unit FullEnvi.t * (Header.t * Loc.t t) list =
  let (is_rec, attr, x, typ_vars, args, typ) = header in
  if Recursivity.to_bool is_rec && attr <> Attribute.CoqRec then
    let var (x : Name.t) env : Loc.t t =
      Variable (Loc.Unknown,
        Envi.bound_name (PathName.of_name [] x) env.FullEnvi.vars) in
    let (x_rec, _) = Envi.fresh (x ^ "_rec") () env.FullEnvi.vars in
    let (counter, _) = Envi.fresh "counter" () env.FullEnvi.vars in
    let args_x_rec =
      (counter,
        Type.Apply (Envi.bound_name (PathName.of_name [] "nat") env.FullEnvi.typs, []))
          :: args in
    let header_x_rec = (is_rec, attr, x_rec, typ_vars, args_x_rec, typ) in
    let env_in_x_rec = Header.env_in_header header_x_rec env in
    let e_x_rec = monadise_let_rec env_in_x_rec e in
    let e_x_rec = Match (Loc.Unknown, var counter env_in_x_rec, [
      (Pattern.Constructor (Envi.bound_name (PathName.of_name [] "O") env_in_x_rec.FullEnvi.constructors, []),
        Apply (Loc.Unknown, var "not_terminated" env_in_x_rec, [Tuple (Loc.Unknown, [])]));
      (Pattern.Constructor (Envi.bound_name (PathName.of_name [] "S") env_in_x_rec.FullEnvi.constructors,
        [Pattern.Variable counter]),
        substitute x
          (Apply (Loc.Unknown, var x_rec env_in_x_rec, [var counter env_in_x_rec])) e_x_rec)]) in
    let env = { env with FullEnvi.vars = Envi.add_name x_rec () env.FullEnvi.vars } in
    let header_x = (Recursivity.New false, Attribute.None, x, typ_vars, args, typ) in
    let env_in_x = Header.env_in_header header_x env in
    let e_x = Apply (Loc.Unknown,
      var x_rec env_in_x,
      Apply (Loc.Unknown, var "read_counter" env_in_x, [Tuple (Loc.Unknown, [])]) ::
      List.map (fun (x, _) -> var x env_in_x) args) in
    let env = { env with FullEnvi.vars = Envi.add_name x () env.FullEnvi.vars } in
    (env, [ (header_x_rec, e_x_rec); (header_x, e_x) ])
  else
    let e = monadise_let_rec (Header.env_in_header header env) e in
    let env = { env with FullEnvi.vars = Envi.add_name x () env.FullEnvi.vars } in
    (env, [(header, e)])

let rec effects (env : Effect.Type.t FullEnvi.t) (e : Loc.t t)
  : (Loc.t * Effect.t) t =
  let compound (es : Loc.t t list) : (Loc.t * Effect.t) t list * Effect.t =
    let es = List.map (effects env) es in
    let effects = List.map (fun e -> snd (annotation e)) es in
    let descriptor = Effect.Descriptor.union (
      List.map (fun effect -> effect.Effect.descriptor) effects) in
    let have_functional_effect = effects |> List.exists (fun effect ->
      not (Effect.Type.is_pure effect.Effect.typ)) in
    if have_functional_effect then
      failwith "Compounds cannot have functional effects."
    else
      (es, { Effect.descriptor = descriptor; typ = Effect.Type.Pure }) in
  match e with
  | Constant (l, c) ->
    let effect =
      { Effect.descriptor = Effect.Descriptor.pure;
        typ = Effect.Type.Pure } in
    Constant ((l, effect), c)
  | Variable (l, x) ->
    (try
      let effect =
        { Effect.descriptor = Effect.Descriptor.pure;
          typ = Envi.find x env.FullEnvi.vars Effect.Type.open_lift } in
      Variable ((l, effect), x)
    with Not_found -> failwith (SmartPrint.to_string 80 2
      (BoundName.pp x ^^ !^ "not found.")))
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
    if List.for_all (fun effect_e_x -> Effect.Type.is_pure effect_e_x.Effect.typ) effects_e_xs then
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
    let env = { env with FullEnvi.vars = Envi.add_name x Effect.Type.Pure env.FullEnvi.vars } in
    let e = effects env e in
    let effect_e = snd (annotation e) in
    let effect = {
      Effect.descriptor = Effect.Descriptor.pure;
      typ = Effect.Type.Arrow (
        effect_e.Effect.descriptor, effect_e.Effect.typ) } in
    Function ((l, effect), x, e)
  | Let (l, ((is_rec, _, x, _, args, _) as header), e1, e2) ->
    let (e1, x_typ) = effects_of_let env is_rec x args e1 in
    let effect1 = snd (annotation e1) in
    let env_in_e2 = { env with FullEnvi.vars = Envi.add_name x x_typ env.FullEnvi.vars } in
    let e2 = effects env_in_e2 e2 in
    let effect2 = snd (annotation e2) in
    let descriptor = Effect.Descriptor.union
      [effect1.Effect.descriptor; effect2.Effect.descriptor] in
    let effect = {
      Effect.descriptor = descriptor;
      typ = effect2.Effect.typ } in
    Let ((l, effect), header, e1, e2)
  | Match (l, e, cases) ->
    let e = effects env e in
    let effect_e = snd (annotation e) in
    if Effect.Type.is_pure effect_e.Effect.typ then
      let cases = cases |> List.map (fun (p, e) ->
        let pattern_vars = Pattern.free_variables p in
        let env = Name.Set.fold (fun x env ->
          { env with FullEnvi.vars = Envi.add_name x Effect.Type.Pure env.FullEnvi.vars })
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
    let effect = { effect_e with
      Effect.descriptor = Effect.Descriptor.remove x effect_e.Effect.descriptor } in
    Run ((l, effect), x, d, e)
  | Return _ | Bind _ | Lift _ ->
    Error.raise Loc.Unknown "Cannot compute effects on an explicit return, bind or lift."

and effects_of_let (env : Effect.Type.t FullEnvi.t) (is_rec : Recursivity.t)
  (x : Name.t) (args : (Name.t * Type.t) list) (e : 'a t)
  : ('a * Effect.t) t * Effect.Type.t =
  let args_names = List.map fst args in
  let env_in_e =
    List.fold_left (fun env x ->
      { env with FullEnvi.vars = Envi.add_name x Effect.Type.Pure env.FullEnvi.vars })
      env args_names in
  if Recursivity.to_bool is_rec then
    let rec fix_effect x_typ =
      let env_in_e = { env with FullEnvi.vars = Envi.add_name x x_typ env_in_e.FullEnvi.vars } in
      let e = effects env_in_e e in
      let effect = snd (annotation e) in
      let x_typ' = Effect.function_typ args_names effect in
      if Effect.Type.eq x_typ x_typ' then
        (e, x_typ)
      else
        fix_effect x_typ' in
    fix_effect Effect.Type.Pure
  else
    let e = effects env_in_e e in
    let effect = snd (annotation e) in
    let x_typ = Effect.function_typ args_names effect in
    (e, x_typ)

let rec monadise (env : unit Envi.t) (e : (Loc.t * Effect.t) t) : Loc.t t =
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
      | Some x -> Let (Loc.Unknown, Header.variable x, e1, e2)
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
        let (x, env) = Envi.fresh "x" () env in
        bind d_e d d e' (Some x) (monadise_list env es d
          (Variable (Loc.Unknown, Envi.bound_name (PathName.of_name [] x) env) :: es') k) in
  (*let rec split_application typ e_xs : t list list =
    match e_xs with
    | [] -> [[]]
    | e_x :: e_xs ->  in*)
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
        let return_descriptor = Effect.Type.return_descriptor effect_f (List.length e_xs) in
        lift return_descriptor d (Apply (l, e_f, e_xs))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | Function ((l, _), x, e) ->
    let env = Envi.add_name x () env in
    Function (l, x, monadise env e)
  | Let ((l, _), (_, _, x, _, [], _), e1, e2) -> (* TODO: use l *)
    let (d1, d2) = (descriptor e1, descriptor e2) in
    let e1 = monadise env e1 in
    let env = Envi.add_name x () env in
    let e2 = monadise env e2 in
    bind d1 d2 d e1 (Some x) e2
  | Let ((l, _), (is_rec, attr, x, typ_args, args, typ), e1, e2) ->
    let typ = match typ with
      | Some typ -> Some (Type.monadise typ (snd (annotation e1)))
      | None -> None in
    let env_in_e1 =
      if Recursivity.to_bool is_rec then
        Envi.add_name x () env
      else
        env in
    let env_in_e1 =
      List.fold_left (fun env_in_e1 (x, _) -> Envi.add_name x () env_in_e1)
        env_in_e1 args in
    let e1 = monadise env_in_e1 e1 in
    let env_in_e2 = Envi.add_name x () env in
    let e2 = monadise env_in_e2 e2 in
    Let (l, (is_rec, attr, x, typ_args, args, typ), e1, e2)
  | Match ((l, _), e, cases) ->
    monadise_list env [e] d [] (fun es' ->
      match es' with
      | [e] ->
        let cases = cases |> List.map (fun (p, e)->
          let env = Name.Set.fold (fun x env -> Envi.add_name x () env)
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
  | Return _ | Bind _ | Lift _ -> failwith "Unexpected arguments for 'monadise'."

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is set). *)
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
      Pp.parens paren @@ nest @@ separate space (BoundName.to_coq x :: List.map (to_coq true) es)
  | Apply (_, e_f, e_xs) ->
    Pp.parens paren @@ nest @@ (separate space (List.map (to_coq true) (e_f :: e_xs)))
  | Function (_, x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | Let (_, (_, _, x, _, [], _), e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^^ !^ ":=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | Let (_, (is_rec, _, f_name, typ_vars, xs, f_typ), e_f, e) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^
      (if Recursivity.to_bool is_rec then !^ "fix" else empty) ^^
      Name.to_coq f_name ^^
      (if typ_vars = []
      then empty
      else braces @@ group (
        separate space (List.map Name.to_coq typ_vars) ^^
        !^ ":" ^^ !^ "Type")) ^^
      group (separate space (xs |> List.map (fun (x, x_typ) ->
        parens (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false x_typ)))) ^^
      (match f_typ with
      | None -> empty
      | Some f_typ -> !^ ":" ^^ Type.to_coq false f_typ) ^^
      !^ ":=" ^^ newline ^^
      indent (to_coq false e_f) ^^ !^ "in" ^^ newline ^^
      to_coq false e)
  | Match (_, e, cases) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline))) ^^
      !^ "end")
  | Record (_, fields) ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
      nest (BoundName.to_coq x ^^ !^ ":=" ^^ to_coq false e))) ^^ !^ "|}")
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
    Pp.parens paren (
      if Effect.Descriptor.is_pure (Effect.Descriptor.remove x d) then
        nest (!^ "unret" ^^ parens output)
      else
        output)
  | Return (_, e) -> Pp.parens paren @@ nest (!^ "ret" ^^ to_coq true e)
  | Bind (_, e1, x, e2) ->
    Pp.parens paren @@ nest (
      !^ "let!" ^^ (match x with
        | None -> !^ "_"
        | Some x -> Name.to_coq x) ^^ !^ ":=" ^^
        to_coq false e1 ^^ !^ "in" ^^ newline ^^
      to_coq false e2)
  | Lift (_, d1, d2, e) ->
    Pp.parens paren @@ nest (
      !^ "lift" ^^ Effect.Descriptor.subset_to_coq d1 d2 ^^ to_coq true e)