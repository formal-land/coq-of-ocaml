(** An expression. *)
open Typedtree
open Types
open SmartPrint

(** The simplified OCaml AST we use. *)
type t =
  | Constant of Constant.t
  | Variable of PathName.t
  | Tuple of t list (** A tuple of expressions. *)
  | Constructor of PathName.t * t list (** A constructor name and a list of arguments. *)
  | Apply of t * t list (** A curryfied application to a list of arguments. *)
  | Function of Name.t * Type.t * t (** An argument name, the type of this argument and a body. *)
  | Let of Name.t * t * t (** A "let" of a non-functional value. *)
  | LetFun of Recursivity.t * Name.t * Name.t list * (Name.t * Type.t) list * Type.t * t * t
    (** A "let" of a function: the recursivity flag, the function name, the type variables,
        the names and types of the arguments, the return type, the body and the expression
        in which we do the "let". We need to group [Let] and [Function] in one constructor
        to make the Coq's fixpoint operator work (and have a nicer pretty-printing). *)
  | Match of t * (Pattern.t * t) list (** Match an expression to a list of patterns. *)
  | Record of (PathName.t * t) list (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t (** Access to a field of a record. *)
  | IfThenElse of t * t * t (** The "else" part may be unit. *)
  | Return of t (** Monadic return. *)
  | Bind of t * Name.t * t (** Monadic bind. *)

(** Take a function expression and make explicit the list of arguments and the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, _, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (e : expression) : t =
  match e.exp_desc with
  | Texp_ident (path, _, _) -> Variable (PathName.of_path path)
  | Texp_constant constant -> Constant (Constant.of_constant constant)
  | Texp_let (rec_flag, [{vb_pat = {pat_desc = Tpat_var (name, _)}; vb_expr = e1}], e2) ->
    let (rec_flag, name, free_typ_vars, args, body_typ, body) =
      import_let_fun rec_flag name e1 in
    let e2 = of_expression e2 in
    if args = [] then
      Let (name, body, e2)
    else
      LetFun (rec_flag, name, free_typ_vars, args, body_typ, body, e2)
  | Texp_function (_, [{c_lhs = {pat_desc = Tpat_var (x, _); pat_type = x_typ}; c_rhs = e}], _) ->
    Function (Name.of_ident x, Type.of_type_expr x_typ, of_expression e)
  | Texp_function (_, cases, _) ->
    let (x, x_typ, e) = open_cases cases in
    Function (x, x_typ, e)
  | Texp_apply (e_f, e_xs) ->
    let e_f = of_expression e_f in
    let e_xs = List.map (fun (_, e_x, _) ->
      match e_x with
      | Some e_x -> of_expression e_x
      | None -> failwith "expected an argument") e_xs in
    Apply (e_f, e_xs)
  | Texp_match (e, cases, _) ->
    let e = of_expression e in
    let cases = List.map (fun {c_lhs = p; c_rhs = e} -> (Pattern.of_pattern p, of_expression e)) cases in
    Match (e, cases)
  | Texp_tuple es -> Tuple (List.map of_expression es)
  | Texp_construct (x, _, es) -> Constructor (PathName.of_loc x, List.map of_expression es)
  | Texp_record (fields, _) -> Record (List.map (fun (x, _, e) -> (PathName.of_loc x, of_expression e)) fields)
  | Texp_field (e, x, _) -> Field (of_expression e, PathName.of_loc x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Constructor ({ PathName.path = []; base = "tt" }, [])
      | Some e3 -> of_expression e3 in
    IfThenElse (of_expression e1, of_expression e2, e3)
  | Texp_try _ | Texp_setfield _ | Texp_array _ | Texp_sequence _
    | Texp_while _ | Texp_for _ | Texp_assert _ ->
    failwith "Imperative expression not handled."
  | _ -> failwith "Expression not handled."
(** Generate a variable and a "match" on this variable from a list of patterns. *)
and open_cases (cases : case list) : Name.t * Type.t * t =
  let x = Name.unsafe_fresh "match_var" in
  let x_typ = Type.Tuple (List.map (fun {c_lhs = {pat_type = typ}} -> Type.of_type_expr typ) cases) in
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
      (Pattern.of_pattern p, of_expression e)) in
  (x, x_typ, Match (Variable (PathName.of_name [] x), cases))
and import_let_fun (rec_flag : Asttypes.rec_flag) (name : Ident.t) (e : expression)
  : Recursivity.t * Name.t * Name.t list * (Name.t * Type.t) list * Type.t * t =
  let name = Name.of_ident name in
  let e_schema = Schema.of_type (Type.of_type_expr e.exp_type) in
  let e = of_expression e in
  let (args_names, e_body) = open_function e in
  let e_typ = e_schema.Schema.typ in
  let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
  (Recursivity.of_rec_flag rec_flag, name, e_schema.Schema.variables,
    List.combine args_names args_typs, e_body_typ, e_body)

(** Do the monadic transformation of an expression using an effects environment. *)
let rec monadise (e : t) (path : PathName.Path.t) (effects : Effect.Env.t)
  : t * Effect.t =
  let var (x : Name.t) : t =
    Variable (PathName.of_name [] x) in
  (** Sequentialize the execution of the [es] expressions and bind their values
      to some variables. The computation of these expressions can generate
      effects but they cannot be functions with effects. [es'] are or variables
      names in case of a bind, else the original expression.
      Then call [k] with the new Effect.Env.tironment and the [es']. *)
  let rec monadise_list (es : t list) (effects : Effect.Env.t)
    (es' : (t * Effect.Type.t) list) (has_effects : bool)
    (k : t list -> Effect.Type.t list -> t * Effect.t)
    : t * Effect.t =
    match es with
    | [] ->
      let (es, es_typs) = List.split @@ List.rev es' in
      let (e, e_effect) = k es es_typs in
      if has_effects && not e_effect.Effect.effect then
        (Return e, { Effect.effect = true; typ = e_effect.Effect.typ })
      else
        (e, e_effect)
    | e :: es ->
      let (e, e_effect) = monadise e path effects in
      if e_effect.Effect.effect then
        let (x, effects) = PathName.fresh "x" e_effect.Effect.typ effects in
        let (final_e, final_e_effect) = monadise_list es effects ((var x, e_effect.Effect.typ) :: es') true k in
        (Bind (e, x, final_e), final_e_effect)
      else
        monadise_list es effects ((e, e_effect.Effect.typ) :: es') has_effects k in
  let compound (es : t list) (k : t list -> t) : t * Effect.t =
    monadise_list es effects [] false (fun es es_typs ->
    if List.for_all Effect.Type.is_pure es_typs then
      (k es, Effect.pure)
    else
      failwith "Elements of compounds cannot have effects") in
  let unify (cases : (Pattern.t option * t) list) : t list * Effect.t =
    let (es, es_effects) = List.split (cases |> List.map (fun (p, e) ->
      let pattern_vars = match p with
        | None -> Name.Set.empty
        | Some p -> Pattern.free_vars p in
      let effects = Name.Set.fold (fun x effects ->
        PathName.Map.add (PathName.of_name path x) Effect.Type.Ground effects)
        pattern_vars effects in
      monadise e path effects)) in
    let rec are_equal effects =
      match effects with
      | effect1 :: effect2 :: effects ->
        effect1.Effect.typ = effect2.Effect.typ && are_equal (effect2 :: effects)
      | _ -> true in
    if are_equal es_effects then
      let effect_typ = match es_effects with
        | [] -> Effect.Type.Ground
        | { Effect.typ = typ } :: _ -> typ in
      let is_effect = List.exists (fun effect -> effect.Effect.effect) es_effects in
      let effect = { Effect.effect = is_effect; typ = effect_typ } in
      if is_effect then
        (List.map2 (fun e effect ->
          if effect.Effect.effect then e else Return e)
          es es_effects,
          effect)
      else
        (es, effect)
    else
      failwith "Effect types are supposed to be equal for unification." in
  match e with
  | Constant _ -> (e, Effect.pure)
  | Variable x ->
    (try (e, { Effect.effect = false; typ = PathName.Map.find x effects })
    with Not_found -> failwith (SmartPrint.to_string 80 2 (PathName.pp x ^^ !^ "not found.")))
  | Tuple es -> compound es (fun es -> Tuple es)
  | Constructor (x, es) -> compound es (fun es -> Constructor (x, es))
  | Apply (e_f, es) ->
    (match es with
    | [] -> monadise e_f path effects
    | [e_x] ->
      monadise_list [e_f; e_x] effects [] false (fun es es_typs ->
        match (es, es_typs) with
        | ([e_f; e_x], [Effect.Type.Arrow (e_f_effect, e_f_typ1, e_f_typ2); e_x_typ]) ->
          if Effect.Type.is_pure e_x_typ then
            (Apply (e_f, [e_x]), { Effect.effect = e_f_effect; typ = e_f_typ2 })
          else
            failwith "Functions cannot be applied to functions with effects."
        | _ -> failwith "Unexpected answer from 'monadise_list'")
    | e :: es -> monadise (Apply (Apply (e_f, [e]), es)) path effects)
  | Function (x, x_typ, e) ->
    let (e, e_effect) = monadise e path (Effect.Env.in_function path effects [x, x_typ]) in
    (Function (x, x_typ, e), { Effect.effect = false;
      typ = Effect.Type.Arrow (e_effect.Effect.effect, Effect.Type.of_type x_typ, e_effect.Effect.typ) })
  | Let (x, e1, e2) ->
    let (e1, e1_effect) = monadise e1 path effects in
    let (e2, e2_effect) = monadise e2 path
      (PathName.Map.add (PathName.of_name path x) e1_effect.Effect.typ effects) in
    if e1_effect.Effect.effect then
      (Bind (e1, x, if e2_effect.Effect.effect then e2 else Return e2),
        { Effect.effect = true; typ = e2_effect.Effect.typ })
    else
      (Let (x, e1, e2), e2_effect)
  | LetFun (is_rec, name, typ_vars, args, e1_typ, e1, e2) ->
    let name_typ = Effect.function_typ args
      { Effect.effect = false; typ = Effect.Type.of_type e1_typ } in
    let effects_in_e1 =
      if Recursivity.to_bool is_rec then
        PathName.Map.add (PathName.of_name path name) name_typ effects
      else
        effects in
    let effects_in_e1 = Effect.Env.in_function path effects_in_e1 args in
    let (e1, e1_effect) = monadise e1 path effects_in_e1 in
    let name_typ = Effect.function_typ args e1_effect in
    let effects_in_e2 = PathName.Map.add (PathName.of_name path name) name_typ effects in
    let (e2, e2_effect) = monadise e2 path effects_in_e2 in
    let e1_typ = Effect.monadise e1_typ e1_effect in
    (LetFun (is_rec, name, typ_vars, args, e1_typ, e1, e2), e2_effect)
  | Match (e, cases) ->
    monadise_list [e] effects [] false (fun es es_typs ->
      match (es, es_typs) with
      | ([e], _) ->
        let (es, effect) = unify (List.map (fun (p, e) -> (Some p, e)) cases) in
        (Match (e, List.map2 (fun e (p, _) -> (p, e)) es cases), effect)
      | _ -> failwith "Unexpected answer from 'monadise_list'.")
  | Record fields ->
    compound (List.map snd fields) (fun es ->
      Record (List.map2 (fun (x, _) e -> (x, e)) fields es))
  | Field (e, f) ->
    monadise_list [e] effects [] false (fun es es_typs ->
      match (es, es_typs) with
      | ([e], [e_typ]) -> (Field (e, f), Effect.pure)
      | _ -> failwith "Unexpected answer from 'monadise_list'.")
  | IfThenElse (e1, e2, e3) ->
    monadise_list [e1] effects [] false (fun es es_typs ->
      match (es, es_typs) with
      | ([e1], _) ->
        let (es, effect) = unify [(None, e2); (None, e3)] in
        (match es with
        | [e2; e3] -> (IfThenElse (e1, e2, e3), effect)
        | _ -> failwith "Unexpected answer from 'unify'.")
      | _ -> failwith "Unexpected answer from 'monadise_list'.")
  | Return _ | Bind _ -> failwith "This expression is already monadic."

let added_vars_in_let_fun (is_rec : Recursivity.t) (f : Name.t)
  (xs : (Name.t * Type.t) list) : Name.Set.t =
  let s = List.fold_left (fun s (x, _) -> Name.Set.add x s) Name.Set.empty xs in
  if Recursivity.to_bool is_rec
  then Name.Set.add f s
  else s

(** Simplify binds of a return and lets of a variable. *)
let simplify (e : t) : t =
  (** The [env] is the environment of substitutions to make. *)
  let rec aux (env : t Name.Map.t) (e : t) : t =
    let rm x = Name.Map.remove x env in
    match e with
    | Bind (Return e1, x, e2) -> aux env (Let (x, e1, e2))
    | Let (x, Variable x', e2) -> aux (Name.Map.add x (Variable x') env) e2
    | Variable x ->
      (match x with
      | { PathName.path = []; base = x } -> if Name.Map.mem x env then Name.Map.find x env else e
      | _ -> e)
    | Constant _ -> e
    | Tuple es -> Tuple (List.map (aux env) es)
    | Constructor (x, es) -> Constructor (x, List.map (aux env) es)
    | Apply (e_f, es) -> Apply (aux env e_f, List.map (aux env) es)
    | Function (x, x_typ, e) -> Function (x, x_typ, aux (rm x) e)
    | Let (x, e1, e2) -> Let (x, aux env e1, aux (rm x) e2)
    | LetFun (is_rec, f, typ_vars, xs, f_typ, e1, e2) ->
      let env_in_f = Name.Set.fold (fun x env ->
        Name.Map.remove x env)
        (added_vars_in_let_fun is_rec f xs)
        env in
      LetFun (is_rec, f, typ_vars, xs, f_typ, aux env_in_f e1, aux (rm f) e2)
    | Match (e, cases) -> Match (aux env e, cases |> List.map (fun (p, e) ->
      let env = Name.Set.fold (fun x env -> Name.Map.remove x env) (Pattern.free_vars p) env in
      (p, aux env e)))
    | Record fields -> Record (fields |> List.map (fun (x, e) -> (x, aux env e)))
    | Field (e, x) -> Field (aux env e, x)
    | IfThenElse (e1, e2, e3) -> IfThenElse (aux env e1, aux env e2, aux env e3)
    | Return e -> Return (aux env e)
    | Bind (e1, x, e2) -> Bind (aux env e1, x, aux (rm x) e2) in
  aux Name.Map.empty e

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq c
  | Variable x -> PathName.to_coq x
  | Tuple es -> parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (x, es) ->
    if es = [] then
      PathName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (PathName.to_coq x :: List.map (to_coq true) es)
  | Apply (e_f, e_xs) ->
    Pp.parens paren @@ nest @@ separate space (List.map (to_coq true) (e_f :: e_xs))
  | Function (x, _, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | Let (x, e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^^ !^ ":=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | LetFun (is_rec, f_name, typ_vars, xs, f_typ, e_f, e) ->
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
      !^ ":" ^^ Type.to_coq false f_typ ^^ !^ ":=" ^^ newline ^^
      indent (to_coq false e_f) ^^ !^ "in" ^^ newline ^^
      to_coq false e)
  | Match (e, cases) ->
    nest (
      !^ "match" ^^ to_coq false e ^^ !^ "with" ^^ newline ^^
      separate space (cases |> List.map (fun (p, e) ->
        nest (!^ "|" ^^ Pattern.to_coq false p ^^ !^ "=>" ^^ to_coq false e ^^ newline))) ^^
      !^ "end")
  | Record fields ->
    nest (!^ "{|" ^^ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, e) ->
      nest (PathName.to_coq x ^^ !^ ":=" ^^ to_coq false e))) ^^ !^ "|}")
  | Field (e, x) -> Pp.parens paren @@ nest (PathName.to_coq x ^^ to_coq true e)
  | IfThenElse (e1, e2, e3) ->
    nest (
      !^ "if" ^^ to_coq false e1 ^^ !^ "then" ^^ newline ^^
      indent (to_coq false e2) ^^ newline ^^
      !^ "else" ^^ newline ^^
      indent (to_coq false e3))
  | Return e -> to_coq paren (Apply (Variable (PathName.of_name [] "ret"), [e]))
  | Bind (e1, x, e2) ->
    Pp.parens paren @@ nest (
      !^ "let!" ^^ Name.to_coq x ^^ !^ ":=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^
      to_coq false e2)