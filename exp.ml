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
    Recursivity.t * Name.t * Name.t list * (Name.t * Type.t) list * Type.t option

  let pp (header : t) : SmartPrint.t =
    let (is_rec, x, typ_vars, args, typ) = header in
    Pp.list [
      Recursivity.pp is_rec; Name.pp x; OCaml.list Name.pp typ_vars;
      OCaml.list (fun (x, typ) -> Pp.list [Name.pp x; Type.pp typ]) args;
      OCaml.option Type.pp typ]

  let variable (x : Name.t) : t =
    (Recursivity.New false, x, [], [], None)
end

(** The simplified OCaml AST we use. *)
type 'a t =
  | Constant of 'a * Constant.t
  | Variable of 'a * PathName.t
  | Tuple of 'a * 'a t list (** A tuple of expressions. *)
  | Constructor of 'a * PathName.t * 'a t list (** A constructor name and a list of arguments. *)
  | Apply of 'a * 'a t * 'a t (** An application. *)
  | Function of 'a * Name.t * 'a t (** An argument name and a body. *)
  | Let of 'a * Header.t * 'a t * 'a t
  | Match of 'a * 'a t * (Pattern.t * 'a t) list (** Match an expression to a list of patterns. *)
  | Record of 'a * (PathName.t * 'a t) list (** Construct a record giving an expression for each field. *)
  | Field of 'a * 'a t * PathName.t (** Access to a field of a record. *)
  | IfThenElse of 'a * 'a t * 'a t * 'a t (** The "else" part may be unit. *)
  | Sequence of 'a * 'a t * 'a t (** A sequence of two expressions. *)
  | Return of 'a * 'a t (** Monadic return. *)
  | Bind of 'a * 'a t * Name.t option * 'a t (** Monadic bind. *)
  | Lift of 'a * Effect.Descriptor.t * Effect.Descriptor.t * 'a t (** Monadic lift. *)

let rec clean (e : 'a t) : unit t =
  match e with
  | Constant (_, c) -> Constant ((), c)
  | Variable (_, x) -> Variable ((), x)
  | Tuple (_, es) -> Tuple ((), List.map clean es)
  | Constructor (_, x, es) -> Constructor ((), x, List.map clean es)
  | Apply (_, e_f, e_x) -> Apply ((), clean e_f, clean e_x)
  | Function (_, x, e) -> Function ((), x, clean e)
  | Let (_, header, e1, e2) -> Let ((), header, clean e1, clean e2)
  | Match (_, e, cases) ->
    Match ((), clean e, List.map (fun (p, e) -> (p, clean e)) cases)
  | Record (_, fields) ->
    Record ((), List.map (fun (x, e) -> (x, clean e)) fields)
  | Field (_, e, x) -> Field ((), clean e, x)
  | IfThenElse (_, e1, e2, e3) -> IfThenElse ((), clean e1, clean e2, clean e3)
  | Sequence (_, e1, e2) -> Sequence ((), clean e1, clean e2)
  | Return (_, e) -> Return ((), clean e)
  | Bind (_, e1, x, e2) -> Bind ((), clean e1, x, clean e2)
  | Lift (_, d1, d2, e) -> Lift ((), d1, d2, clean e)

let rec pp (pp_a : 'a -> SmartPrint.t) (e : 'a t) : SmartPrint.t =
  let pp = pp pp_a in
  match e with
  | Constant (a, c) -> nest (!^ "Constant" ^^ Pp.list [pp_a a; Constant.pp c])
  | Variable (a, x) -> nest (!^ "Variable" ^^ Pp.list [pp_a a; PathName.pp x])
  | Tuple (a, es) ->
    nest (!^ "Tuple" ^^ Pp.list (pp_a a :: List.map pp es))
  | Constructor (a, x, es) ->
    nest (!^ "Constructor" ^^ Pp.list (pp_a a :: PathName.pp x :: List.map pp es))
  | Apply (a, e_f, e_x) ->
    nest (!^ "Apply" ^^ Pp.list [pp_a a; pp e_f; pp e_x])
  | Function (a, x, e) ->
    nest (!^ "Function" ^^ Pp.list [pp_a a; Name.pp x; pp e])
  | Let (a, header, e1, e2) ->
    nest (!^ "Let" ^^ pp_a a ^^ Header.pp header ^^ !^ "=" ^^ newline ^^
      indent (pp e1) ^^ !^ "in" ^^ newline ^^
      pp e2)
  | Match (a, e, cases) ->
    nest (!^ "Match" ^^ Pp.list [pp_a a; pp e;
      cases |> OCaml.list (fun (p, e) ->
        nest @@ parens (Pattern.pp p ^-^ !^ "," ^^ pp e))])
  | Record (a, fields) ->
    nest (!^ "Record" ^^ Pp.list (pp_a a :: (fields |> List.map (fun (x, e) ->
      nest @@ parens (PathName.pp x ^-^ !^ "," ^^ pp e)))))
  | Field (a, e, x) ->
    nest (!^ "Field" ^^ Pp.list [pp_a a; pp e; PathName.pp x])
  | IfThenElse (a, e1, e2, e3) ->
    nest (!^ "IfThenElse" ^^ Pp.list [pp_a a; pp e1; pp e2; pp e3])
  | Sequence (a, e1, e2) ->
    nest (!^ "Sequence" ^^ Pp.list [pp_a a; pp e1; pp e2])
  | Return (a, e) -> nest (!^ "Return" ^^ Pp.list [pp_a a; pp e])
  | Bind (a, e1, x, e2) -> nest (!^ "Bind" ^^ Pp.list
    [pp_a a; pp e1; nest (OCaml.option Name.pp x); pp e2])
  | Lift (a, d1, d2, e) ->
    nest (!^ "Lift" ^^
      Pp.list [pp_a a; Effect.Descriptor.pp d1; Effect.Descriptor.pp d2; pp e])

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : 'a t) : Name.t list * 'a t =
  match e with
  | Function (_, x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (env : unit PathName.Env.t) (e : expression) : unit t =
  match e.exp_desc with
  | Texp_ident (path, _, _) -> Variable ((), PathName.of_path path)
  | Texp_constant constant -> Constant ((), Constant.of_constant constant)
  | Texp_let (rec_flag, [{ vb_pat = pattern; vb_expr = e1 }], e2) ->
    let (rec_flag, pattern, free_typ_vars, args, body_typ, body) =
      import_let_fun env rec_flag pattern e1 in
    let env_in_e2 = Name.Set.fold (fun x env -> PathName.Env.add_name x () env)
      (Pattern.free_variables pattern) env in
    let e2 = of_expression env_in_e2 e2 in
    (match (pattern, args) with
    | (Pattern.Variable name, []) ->
      Let ((), (Recursivity.New false, name, [], [], None), body, e2)
    | (_, []) -> Match ((), body, [pattern, e2])
    | (Pattern.Variable name, _) ->
      Let ((), (rec_flag, name, free_typ_vars, args, Some body_typ), body, e2)
    | _ -> failwith "Cannot match a function definition on a pattern.")
  | Texp_function (_, [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}], _)
  | Texp_function (_, [{c_lhs = { pat_desc = Tpat_alias
    ({ pat_desc = Tpat_any }, x, _)}; c_rhs = e}], _) ->
    let x = Name.of_ident x in
    Function ((), x, of_expression (PathName.Env.add_name x () env) e)
  | Texp_function (_, cases, _) ->
    let (x, e) = open_cases env cases in
    Function ((), x, e)
  | Texp_apply (e_f, e_xs) ->
    let e_f = of_expression env e_f in
    let e_xs = List.map (fun (_, e_x, _) ->
      match e_x with
      | Some e_x -> of_expression env e_x
      | None -> failwith "expected an argument") e_xs in
    (match (e_f, e_xs) with
    | (Variable (_, x), [Constructor (_, exn, es)])
      when x = PathName.of_name ["Pervasives"] "raise" ->
      Apply ((), Variable ((), exn), Tuple ((), es))
    | _ -> List.fold_left (fun e e_x -> Apply ((), e, e_x)) e_f e_xs)
  | Texp_match (e, cases, _) ->
    let e = of_expression env e in
    let cases = List.map (fun {c_lhs = p; c_rhs = e} ->
      let p = Pattern.of_pattern p in
      let env_in_e =
        Name.Set.fold (fun x env -> PathName.Env.add_name x () env)
          (Pattern.free_variables p) env in
      (p, of_expression env_in_e e)) cases in
    Match ((), e, cases)
  | Texp_tuple es -> Tuple ((), List.map (of_expression env) es)
  | Texp_construct (x, _, es) ->
    Constructor ((), PathName.of_loc x, List.map (of_expression env) es)
  | Texp_record (fields, _) ->
    Record ((), fields |> List.map (fun (x, _, e) ->
      (PathName.of_loc x, of_expression env e)))
  | Texp_field (e, x, _) -> Field ((), of_expression env e, PathName.of_loc x)
  | Texp_ifthenelse (e1, e2, e3) ->
    let e3 = match e3 with
      | None -> Tuple ((), [])
      | Some e3 -> of_expression env e3 in
    IfThenElse ((), of_expression env e1, of_expression env e2, e3)
  | Texp_sequence (e1, e2) ->
    Sequence ((), of_expression env e1, of_expression env e2)
  | Texp_try _ | Texp_setfield _ | Texp_array _
    | Texp_while _ | Texp_for _ | Texp_assert _ ->
    failwith "Imperative expression not handled."
  | _ -> failwith "Expression not handled."
(** Generate a variable and a "match" on this variable from a list of patterns. *)
and open_cases (env : unit PathName.Env.t) (cases : case list)
  : Name.t * unit t =
  let (x, env) = PathName.Env.fresh "match_var" () env in
  let cases = cases |> List.map (fun {c_lhs = p; c_rhs = e} ->
    let p = Pattern.of_pattern p in
    let env = Name.Set.fold (fun x env -> PathName.Env.add_name x () env)
      (Pattern.free_variables p) env in
    (p, of_expression env e)) in
  (x, Match ((), Variable ((), PathName.of_name [] x), cases))
and import_let_fun (env : unit PathName.Env.t) (rec_flag : Asttypes.rec_flag)
  (pattern : pattern) (e : expression)
  : Recursivity.t * Pattern.t * Name.t list * (Name.t * Type.t) list
    * Type.t * unit t =
  let rec_flag = Recursivity.of_rec_flag rec_flag in
  let pattern = Pattern.of_pattern pattern in
  let e_schema = Schema.of_type (Type.of_type_expr e.exp_type) in
  let env_in_e =
    if Recursivity.to_bool rec_flag then
      Name.Set.fold (fun x env -> PathName.Env.add_name x () env)
        (Pattern.free_variables pattern) env
    else
      env in
  let e = of_expression env_in_e e in
  let (args_names, e_body) = open_function e in
  let e_typ = e_schema.Schema.typ in
  let (args_typs, e_body_typ) = Type.open_type e_typ (List.length args_names) in
  (rec_flag, pattern, e_schema.Schema.variables,
    List.combine args_names args_typs, e_body_typ, e_body)

let rec substitute (x : PathName.t) (e' : 'a t) (e : 'a t) : 'a t =
  match e with
  | Constant _ -> e
  | Variable (_, y) -> if x = y then e' else e
  | Tuple (a, es) -> Tuple (a, List.map (substitute x e') es)
  | Constructor (a, y, es) -> Constructor (a, y, List.map (substitute x e') es)
  | Apply (a, e1, e2) -> Apply (a, substitute x e' e1, substitute x e' e2)
  | Function (a, y, e) ->
    if PathName.of_name [] y = x then
      Function (a, y, e)
    else
      Function (a, y, substitute x e' e)
  | Let (a, (is_rec, y, typ_args, args, typ), e1, e2) ->
    let e1 =
      if (Recursivity.to_bool is_rec && PathName.of_name [] y = x)
        || List.exists (fun (y, _) -> PathName.of_name [] y = x) args then
        e1
      else
        substitute x e' e1 in
    let e2 =
      if PathName.of_name [] y = x then
        e2
      else
        substitute x e' e2 in
    Let (a, (is_rec, y, typ_args, args, typ), e1, e2)
  | Match (a, e, cases) ->
    let e = substitute x e' e in
    let cases = cases |> List.map (fun (p, e) ->
      let ys = Pattern.free_variables p in
      if Name.Set.exists (fun y -> PathName.of_name [] y = x) ys then
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
  | Return (a, e) -> Return (a, substitute x e' e)
  | Bind (a, e1, y, e2) ->
    let e1 = substitute x e' e1 in
    let e2 =
      match y with
      | None -> substitute x e' e2
      | Some y ->
        if PathName.of_name [] y = x then
          e2
        else
          substitute x e' e2 in
    Bind (a, e1, y, e2)
  | Lift (a, d1, d2, e) -> Lift (a, d1, d2, substitute x e' e)

let rec monadise_let_rec (env : unit PathName.Env.t) (e : unit t) : unit t =
  match e with
  | Constant _ | Variable _ -> e
  | Tuple (_, es) -> Tuple ((), List.map (monadise_let_rec env) es)
  | Constructor (_, x, es) ->
    Constructor ((), x, List.map (monadise_let_rec env) es)
  | Apply (_, e1, e2) ->
    Apply ((), monadise_let_rec env e1, monadise_let_rec env e2)
  | Function (_, x, e) -> Function ((), x, monadise_let_rec env e)
  | Let (_, header, e1, e2) ->
    let defs = monadise_let_rec_definition env header e1 in
    let e2 = monadise_let_rec env e2 in
    List.fold_right (fun (header, e) e2 -> Let ((), header, e, e2)) defs e2
  | Match (_, e, cases) ->
    Match ((), monadise_let_rec e,
      List.map (fun (p, e) -> (p, monadise_let_rec e)) cases)
  | Record (_, fields) ->
    Record ((), List.map (fun (x, e) -> (x, monadise_let_rec e)) fields)
  | Field (_, e, x) -> Field ((), monadise_let_rec e, x)
  | IfThenElse (_, e1, e2, e3) ->
    IfThenElse ((), monadise_let_rec e1, monadise_let_rec e2,
      monadise_let_rec e3)
  | Sequence (_, e1, e2) ->
    Sequence ((), monadise_let_rec e1, monadise_let_rec e2)
  | Return (_, e) -> monadise_let_rec e
  | Bind (_, e1, x, e2) ->
    Bind ((), monadise_let_rec e1, x, monadise_let_rec e2)
  | Lift (_, d1, d2, e) -> Lift ((), d1, d2, monadise_let_rec e)

and monadise_let_rec_definition (env : unit PathName.Env.t) (header : Header.t)
  (e : unit t) : (Header.t * unit t) list =
  let (is_rec, x, typ_vars, args, typ) = header in
  let e = monadise_let_rec e in
  if Recursivity.to_bool is_rec then
    let var (x : Name.t) : unit t = Variable ((), PathName.of_name [] x) in
    let (x_rec, env) = PathName.Env.fresh (x ^ "_rec") () env in
    let args' =
      ("counter", Type.Apply (PathName.of_name [] "nat", [])) :: args in
    let e = Match (var "counter", [
      (Pattern.Constant (Constant.Nat 0),
        Apply (var "not_terminated", var "tt"));
      (Pattern.Constructor (PathName.of_name [] "S",
        [Pattern.Variable "counter"]),
        substitute (PathName.of_name [] x)
          (Apply (var x_rec, var "counter")) e)]) in
    [ ((is_rec, x_rec, typ_vars, args', typ), e);
      ((Recursivity.New false, x, typ_vars, args, typ),
        Let (Header.variable "counter",
          Apply (var "read_counter", var "tt"),
        List.fold_left (fun e (x, _) -> Apply (e, var x))
          (Apply (var x_rec, var "counter")) args)) ]
  else
    [(header, e)]

module Tree = struct
  type t =
    | Leaf of Effect.t
    | Compound of t list * Effect.t
    | Apply of t * t * Effect.t
    | Function of t * Effect.t
    | Let of t * t * Effect.t
    | Match of t * t list * Effect.t
    | Field of t * Effect.t
    | Sequence of t * t * Effect.t

  let effect (tree : t) : Effect.t =
    match tree with
    | Leaf effect | Compound (_, effect) | Apply (_, _, effect)
      | Function (_, effect) | Let (_, _, effect) | Match (_, _, effect)
      | Field (_, effect) | Sequence (_, _, effect) -> effect

  let descriptor (tree : t) : Effect.Descriptor.t =
    (effect tree).Effect.descriptor

  let rec pp (tree : t) : SmartPrint.t =
    let aux constructor trees =
      nest (!^ constructor ^^ Pp.list (
        Effect.pp (effect tree) :: List.map pp trees)) in
    match tree with
    | Leaf _ -> aux "Leaf" []
    | Compound (trees, _) -> aux "Compound" trees
    | Apply (tree1, tree2, _) -> aux "Apply" [tree1; tree2]
    | Function (tree, _) -> aux "Function" [tree]
    | Let (tree1, tree2, _) -> aux "Let" [tree1; tree2]
    | Match (tree, trees, _) -> aux "Match" (tree :: trees)
    | Field (tree, _) -> aux "Field" [tree]
    | Sequence (tree1, tree2, _) -> aux "Sequence" [tree1; tree2]
end

let rec to_tree (effects : Effect.Env.t) (e : t) : Tree.t =
  let compound (es : t list) : Tree.t =
    let trees = List.map (to_tree effects) es in
    let effects = List.map Tree.effect trees in
    let descriptor = Effect.Descriptor.union (
      List.map (fun effect -> effect.Effect.descriptor) effects) in
    let have_functional_effect = effects |> List.exists (fun effect ->
      not (Effect.Type.is_pure effect.Effect.typ)) in
    if have_functional_effect then
      failwith "Compounds cannot have functional effects."
    else
      Tree.Compound (trees,
        { Effect.descriptor = descriptor; typ = Effect.Type.Pure }) in
  match e with
  | Constant _ -> Tree.Leaf
    { Effect.descriptor = Effect.Descriptor.pure;
      typ = Effect.Type.Pure }
  | Variable x ->
    (try Tree.Leaf
      { Effect.descriptor = Effect.Descriptor.pure;
        typ = Effect.Env.find x effects }
    with Not_found -> failwith (SmartPrint.to_string 80 2
      (PathName.pp x ^^ !^ "not found.")))
  | Tuple es | Constructor (_, es) -> compound es
  | Apply (e_f, e_x) ->
    let tree_f = to_tree effects e_f in
    let effect_f = Tree.effect tree_f in
    let tree_x = to_tree effects e_x in
    let effect_x = Tree.effect tree_x in
    if Effect.Type.is_pure effect_x.Effect.typ then
      let descriptor = Effect.Descriptor.union [
        effect_f.Effect.descriptor; effect_x.Effect.descriptor;
        Effect.Type.return_descriptor effect_f.Effect.typ] in
      let effect_typ = Effect.Type.return_type effect_f.Effect.typ in
      Tree.Apply (tree_f, tree_x,
        { Effect.descriptor = descriptor; typ = effect_typ })
    else
      failwith "Function arguments cannot have functional effects."
  | Function (x, e) ->
    let tree_e = to_tree (Effect.Env.add (PathName.of_name [] x)
      Effect.Type.Pure effects) e in
    let effect_e = Tree.effect tree_e in
    Tree.Function (tree_e,
      { Effect.descriptor = Effect.Descriptor.pure;
        typ = Effect.Type.Arrow (
          effect_e.Effect.descriptor, effect_e.Effect.typ) })
  | Let ((is_rec, x, _, args, _), e1, e2) ->
    let (tree1, x_typ) = to_tree_let_fun effects is_rec x args e1 in
    let effect1 = Tree.effect tree1 in
    let effects_in_e2 = Effect.Env.add (PathName.of_name [] x) x_typ effects in
    let tree2 = to_tree effects_in_e2 e2 in
    let effect2 = Tree.effect tree2 in
    let descriptor = Effect.Descriptor.union
      [effect1.Effect.descriptor; effect2.Effect.descriptor] in
    Tree.Let (tree1, tree2,
      { Effect.descriptor = descriptor;
        typ = effect2.Effect.typ })
  | Match (e, cases) ->
    let tree_e = to_tree effects e in
    let effect_e = Tree.effect tree_e in
    if Effect.Type.is_pure effect_e.Effect.typ then
      let trees = cases |> List.map (fun (p, e) ->
        let pattern_vars = Pattern.free_variables p in
        let effects = Name.Set.fold (fun x effects ->
          Effect.Env.add (PathName.of_name [] x) Effect.Type.Pure effects)
          pattern_vars effects in
        to_tree effects e) in
      let effect = Effect.union (List.map Tree.effect trees) in
      Tree.Match (tree_e, trees,
        { Effect.descriptor = Effect.Descriptor.union
            [effect_e.Effect.descriptor; effect.Effect.descriptor];
          typ = effect.Effect.typ })
    else
      failwith "Cannot match a value with functional effects."
  | Record fields -> compound (List.map snd fields)
  | Field (e, _) ->
    let tree = to_tree effects e in
    let effect = Tree.effect tree in
    if Effect.Type.is_pure effect.Effect.typ then
      Tree.Field (tree, effect)
    else
      failwith "Cannot take a field of a value with functional effects."
  | IfThenElse (e1, e2, e3) ->
    let tree_e1 = to_tree effects e1 in
    let effect_e1 = Tree.effect tree_e1 in
    if Effect.Type.is_pure effect_e1.Effect.typ then
      let trees = List.map (to_tree effects) [e2; e3] in
      let effect = Effect.union (List.map Tree.effect trees) in
      Tree.Match (tree_e1, trees,
        { Effect.descriptor = Effect.Descriptor.union
            [effect_e1.Effect.descriptor; effect.Effect.descriptor];
          typ = effect.Effect.typ })
    else
      failwith "Cannot do an if on a value with functional effects."
  | Sequence (e1, e2) ->
    let tree_e1 = to_tree effects e1 in
    let effect_e1 = Tree.effect tree_e1 in
    let tree_e2 = to_tree effects e2 in
    let effect_e2 = Tree.effect tree_e2 in
    Tree.Sequence (tree_e1, tree_e2,
      { Effect.descriptor = Effect.Descriptor.union
          [effect_e1.Effect.descriptor; effect_e2.Effect.descriptor];
        typ = effect_e2.Effect.typ })
  | Return _ | Bind _ | Lift _ ->
    failwith "Cannot compute effects on an explicit return, bind or lift."

  and to_tree_let_fun (effects : Effect.Env.t)
    (is_rec : Recursivity.t) (x : Name.t) (args : (Name.t * Type.t) list)
    (e : t) : Tree.t * Effect.Type.t =
    let args_names = List.map fst args in
    let effects_in_e = Effect.Env.in_function effects args_names in
    if Recursivity.to_bool is_rec then
      let rec fix_tree x_typ =
        let effects_in_e = Effect.Env.add (PathName.of_name [] x)
          x_typ effects_in_e in
        let tree = to_tree effects_in_e e in
        let effect = Tree.effect tree in
        let x_typ' = Effect.function_typ args_names effect in
        if Effect.Type.eq x_typ x_typ' then
          (tree, x_typ)
        else
          fix_tree x_typ' in
      fix_tree Effect.Type.Pure
    else
      let tree = to_tree effects_in_e e in
      let effect = Tree.effect tree in
      let x_typ = Effect.function_typ args_names effect in
      (tree, x_typ)

let rec monadise (env : PathName.Env.t) (e : t) (tree : Tree.t) : t =
  let var (x : Name.t) : t = Variable (PathName.of_name [] x) in
  let lift d1 d2 e =
    if Effect.Descriptor.eq d1 d2 then
      e
    else if Effect.Descriptor.is_pure d1 then
      Return e
    else
      Lift (d1, d2, e) in
  (** [d1] is the descriptor of [e1], [d2] of [e2]. *)
  let bind d1 d2 d e1 x e2 =
    if Effect.Descriptor.is_pure d1 then
      match x with
      | Some x -> Let (Header.variable x, e1, e2)
      | None -> e2
    else
      Bind (lift d1 d e1, x, lift d2 d e2) in
  (** [k es'] is supposed to raise the effect [d]. *)
  let rec monadise_list env es trees d es' k =
    match (es, trees) with
    | ([], []) -> k (List.rev es')
    | (e :: es, tree :: trees) ->
      let d_e = Tree.descriptor tree in
      if Effect.Descriptor.is_pure d_e then
        monadise_list env es trees d (e :: es') k
      else
        let e' = monadise env e tree in
        let (x, env) = PathName.Env.fresh "x" env in
        bind d_e d d e' (Some x)
          (monadise_list env es trees d (var x :: es') k)
    | _ -> failwith "Unexpected number of trees." in
  let d = Tree.descriptor tree in
  match (e, tree) with
  | (Constant _, Tree.Leaf _) | (Variable _, Tree.Leaf _) -> e
  | (Tuple es, Tree.Compound (trees, _)) ->
    monadise_list env es trees d [] (fun es' ->
      lift Effect.Descriptor.pure d (Tuple es'))
  | (Constructor (x, es), Tree.Compound (trees, _)) ->
    monadise_list env es trees d [] (fun es' ->
      lift Effect.Descriptor.pure d (Constructor (x, es')))
  | (Apply (e1, e2), Tree.Apply (tree1, tree2, _)) ->
    monadise_list env [e1; e2] [tree1; tree2] d [] (fun es' ->
      match es' with
      | [e1; e2] ->
        let return_descriptor =
          Effect.Type.return_descriptor (Tree.effect tree1).Effect.typ in
        lift return_descriptor d (Apply (e1, e2))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | (Function (x, e), Tree.Function (tree, _)) ->
    let env = PathName.Env.add (PathName.of_name [] x) env in
    Function (x, monadise env e tree)
  | (Let ((_, x, _, [], _), e1, e2), Tree.Let (tree1, tree2, _)) ->
    let e1 = monadise env e1 tree1 in
    let env = PathName.Env.add (PathName.of_name [] x) env in
    let e2 = monadise env e2 tree2 in
    bind (Tree.descriptor tree1) (Tree.descriptor tree2) d e1 (Some x) e2
  | (Let ((is_rec, x, typ_args, args, Some typ), e1, e2),
    Tree.Let (tree1, tree2, _)) ->
    let typ = Type.monadise typ (Tree.effect tree1) in
    let env_in_e1 =
      if Recursivity.to_bool is_rec then
        PathName.Env.add (PathName.of_name [] x) env
      else
        env in
    let e1 = monadise env_in_e1 e1 tree1 in
    let env_in_e2 = PathName.Env.add (PathName.of_name [] x) env in
    let e2 = monadise env_in_e2 e2 tree2 in
    Let ((is_rec, x, typ_args, args, Some typ), e1, e2)
  | (Match (e, cases), Tree.Match (tree, trees, _)) ->
    monadise_list env [e] [tree] d [] (fun es' ->
      match es' with
      | [e] ->
        let cases = List.map2 (fun (p, e) tree ->
          let env = Name.Set.fold (fun x env ->
            PathName.Env.add (PathName.of_name [] x) env)
            (Pattern.free_variables p) env in
          (p, lift (Tree.descriptor tree) d (monadise env e tree)))
          cases trees in
        Match (e, cases)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | (Record fields, Tree.Compound (trees, _)) ->
    monadise_list env (List.map snd fields) trees d [] (fun es' ->
      let fields = List.map2 (fun (f, _) e -> (f, e)) fields es' in
      lift Effect.Descriptor.pure d (Record fields))
  | (Field (e, x), Tree.Field (tree, _)) ->
    monadise_list env [e] [tree] d [] (fun es' ->
      match es' with
      | [e] -> lift Effect.Descriptor.pure d (Field (e, x))
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | (IfThenElse (e1, e2, e3), Tree.Match (tree1, [tree2; tree3], _)) ->
    monadise_list env [e1] [tree1] d [] (fun es' ->
      match es' with
      | [e1] ->
        let e2 = lift (Tree.descriptor tree2) d (monadise env e2 tree2) in
        let e3 = lift (Tree.descriptor tree3) d (monadise env e3 tree3) in
        IfThenElse (e1, e2, e3)
      | _ -> failwith "Wrong answer from 'monadise_list'.")
  | (Sequence (e1, e2), Tree.Sequence (tree1, tree2, _)) ->
    let e1 = monadise env e1 tree1 in
    let e2 = monadise env e2 tree2 in
    bind (Tree.descriptor tree1) (Tree.descriptor tree2) d e1 None e2
  | _ -> failwith "Unexpected arguments for 'monadise'."
 
(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq c
  | Variable x -> PathName.to_coq x
  | Tuple es ->
    if es = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq true) es)
  | Constructor (x, es) ->
    if es = [] then
      PathName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (PathName.to_coq x :: List.map (to_coq true) es)
  | Apply (e_f, e_x) ->
    Pp.parens paren @@ nest @@ (to_coq true e_f ^^ to_coq true e_x)
  | Function (x, e) ->
    Pp.parens paren @@ nest (!^ "fun" ^^ Name.to_coq x ^^ !^ "=>" ^^ to_coq false e)
  | Let ((_, x, _, [], _), e1, e2) ->
    Pp.parens paren @@ nest (
      !^ "let" ^^ Name.to_coq x ^^ !^ ":=" ^^ to_coq false e1 ^^ !^ "in" ^^ newline ^^ to_coq false e2)
  | Let ((is_rec, f_name, typ_vars, xs, f_typ), e_f, e) ->
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
  | Sequence (e1, e2) ->
    nest (to_coq true e1 ^-^ !^ ";" ^^ newline ^^ to_coq false e2)
  | Return e -> Pp.parens paren @@ nest (!^ "ret" ^^ to_coq true e)
  | Bind (e1, x, e2) ->
    Pp.parens paren @@ nest (
      !^ "let!" ^^ (match x with
        | None -> !^ "_"
        | Some x -> Name.to_coq x) ^^ !^ ":=" ^^
        to_coq false e1 ^^ !^ "in" ^^ newline ^^
      to_coq false e2)
  | Lift (d1, d2, e) ->
    Pp.parens paren @@ nest (
      !^ "lift" ^^ Effect.Descriptor.subset_to_coq d1 d2 ^^ to_coq true e)