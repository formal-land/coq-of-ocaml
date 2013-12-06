(** An expression. *)
open Typedtree
open Types
open PPrint

(** The simplified OCaml AST we use. *)
type t =
  | Constant of Constant.t
  | Variable of PathName.t
  | Tuple of t list (** A tuple of expressions. *)
  | Constructor of PathName.t * t list (** A constructor name and a list of arguments. *)
  | Apply of t * t list (** A curryfied application to a list of arguments. *)
  | Function of Name.t * t (** An argument name and a body. *)
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
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (e : expression) : t =
  let loc = e.exp_loc.Location.loc_start in
  let (file_name, l, c) = Location.get_pos_info loc in
  print_endline file_name;
  match e.exp_desc with
  | Texp_ident (path, _, _) -> Variable (PathName.of_path path)
  | Texp_constant constant -> Constant (Constant.of_constant constant)
  | Texp_let (rec_flag, [{vb_pat = {pat_desc = Tpat_var (x, _)}; vb_expr = e1}], e2) ->
    let e1_schema = Schema.of_type (Type.of_type_expr e1.exp_type) in
    let e1_typ = e1_schema.Schema.typ in
    let x = Name.of_ident x in
    let e1 = of_expression e1 in
    let e2 = of_expression e2 in
    let (arg_names, e1_body) = open_function e1 in
    if arg_names = [] then
      Let (x, e1, e2)
    else
      let (arg_typs, e1_body_typ) = Type.open_function e1_typ (List.length arg_names) in
      LetFun (Recursivity.of_rec_flag rec_flag, x, e1_schema.Schema.variables, List.combine arg_names arg_typs, e1_body_typ, e1_body, e2)
  | Texp_function (_, [{c_lhs = {pat_desc = Tpat_var (x, _)}; c_rhs = e}], _) -> Function (Name.of_ident x, of_expression e)
  | Texp_function (_, cases, _) ->
    let (x, e) = open_cases cases in
    Function (x, e)
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
  | Texp_try _ | Texp_setfield _ | Texp_array _ | Texp_sequence _ | Texp_while _ | Texp_for _ | Texp_assert _ ->
    failwith "Imperative expression not handled."
  | _ -> failwith "Expression not handled."
(** Generate a variable and a "match" on this variable from a list of patterns. *)
and open_cases (cases : case list) : Name.t * t =
  let cases = List.map (fun {c_lhs = p; c_rhs = e} -> (Pattern.of_pattern p, of_expression e)) cases in
  let x = Name.unsafe_fresh "match_var" in
  (x, Match (Variable (PathName.of_name [] x), cases))

let added_vars_in_let_fun (is_rec : Recursivity.t) (f : Name.t) (xs : (Name.t * Type.t) list) : Name.Set.t =
  let s = List.fold_left (fun s (x, _) -> Name.Set.add x s) Name.Set.empty xs in
  if is_rec = Recursivity.Recursive
  then Name.Set.add f s
  else s

(** Free variables of an expression (we do not consider variables with a path referencing other modules). *)
let rec free_vars (e : t) : Name.Set.t =
  let free_vars_of_list es =
    List.fold_left (fun s e -> Name.Set.union s (free_vars e)) Name.Set.empty es in
  match e with
  | Constant _ -> Name.Set.empty
  | Variable { PathName.path = []; base = x } -> Name.Set.singleton x
  | Variable _ -> Name.Set.empty
  | Tuple es | Constructor (_, es) -> free_vars_of_list es
  | Apply (e_f, es) -> free_vars_of_list (e_f :: es)
  | Function (x, e) -> Name.Set.remove x (free_vars e)
  | Let (x, e1, e2) | Bind (e1, x, e2) -> Name.Set.union (free_vars e1) (Name.Set.remove x (free_vars e2))
  | LetFun (is_rec, f, _, xs, _, e1, e2) ->
    let s_e1 = Name.Set.diff (free_vars e1) (added_vars_in_let_fun is_rec f xs) in
    Name.Set.union s_e1 (Name.Set.remove f (free_vars e2))
  | Match (e, cases) ->
    let s_e = free_vars e in
    let s_cases = cases |> List.fold_left (fun s (pattern, e) ->
      Name.Set.union s (Name.Set.diff (free_vars e) (Pattern.free_vars pattern)))
      Name.Set.empty in
    Name.Set.union s_e s_cases
  | Record fields -> free_vars_of_list (List.map snd fields)
  | Field (e, _) | Return e -> free_vars e
  | IfThenElse (e1, e2, e3) -> free_vars_of_list [e1; e2; e3]

(** Do the monadic transformation of an expression. *)
let monadise (e : t) : t =
  (** The [env] is the set of current free variables. *)
  let rec aux (e : t) (env : Name.Set.t) : t =
    let var (x : Name.t) : t =
      Variable (PathName.of_name [] x) in
    (** Sequentialize the execution of the [es] expressions and bind their values to [xs].
        Then call [k] with the [xs] and the new environment. *)
    let rec aux_list (es : t list) (env : Name.Set.t) (xs : Name.t list)
      (k : Name.Set.t -> Name.t list -> t) : t =
      match es with
      | [] -> k env (List.rev xs)
      | e :: es ->
        let (x, env') = Name.fresh "x" env in
        Bind (aux e env, x, aux_list es env' (x :: xs) k) in
    match e with
    | Constant _ | Variable _ -> Return e
    | Tuple es -> aux_list es env [] (fun _ xs ->
        Return (Tuple (List.map var xs)))
    | Constructor (x, es) -> aux_list es env [] (fun _ xs ->
        Return (Constructor (x, List.map var xs)))
    | Apply (e_f, es) ->
      (match es with
      | [] -> aux e_f env
      | [e_x] ->
        let (f, env') = Name.fresh "f" env in
        let (x, env') = Name.fresh "x" env' in
        Bind (aux e_f env, f,
        Bind (aux e_x env, x,
        Apply (var f, [var x])))
      | e :: es -> aux (Apply (Apply (e_f, [e]), es)) env)
    | Function (x, e) -> Return (Function (x, aux e (Name.Set.add x env)))
    | Let (x, e1, e2) -> Bind (aux e1 env, x, aux e2 (Name.Set.add x env))
    | LetFun (is_rec, f, typ_vars, xs, f_typ, e1, e2) ->
      let e1 = aux e1 (Name.Set.union env (added_vars_in_let_fun is_rec f xs)) in
      let e2 = aux e2 (Name.Set.add f env) in
      let xs = xs |> List.map (fun (x, typ) -> (x, Type.monadise typ)) in
      LetFun (is_rec, f, typ_vars, xs, Type.Monad (Type.monadise f_typ), e1, e2)
    | Match (e, cases) ->
      let (x, env') = Name.fresh "x" env in
      Bind (aux e env, x, Match (var x, cases |> List.map (fun (pattern, e) ->
        (pattern, aux e (Name.Set.union env' (Pattern.free_vars pattern))))))
    | Record fields -> aux_list (List.map snd fields) env [] (fun env xs ->
      Return (Record (List.map2 (fun (f, _) x -> (f, var x)) fields xs)))
    | Field (e, f) ->
      let (x, _) = Name.fresh "x" env in
      Bind (aux e env, x,
      Return (Field (var x, f)))
    | IfThenElse (e1, e2, e3) ->
      let (x, env') = Name.fresh "x" env in
      Bind (aux e1 env, x,
      IfThenElse (var x, aux e2 env', aux e3 env'))
    | Return _ | Bind _ -> failwith "This expression is already monadic." in
  aux e (free_vars e)

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
    | Function (x, e) -> Function (x, aux (rm x) e)
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

(** Pretty-print an expression (inside parenthesis if the [paren] flag is set). *)
let rec pp (paren : bool) (e : t) : document =
  match e with
  | Constant c -> Constant.pp c
  | Variable x -> PathName.pp x
  | Tuple es -> group (lparen ^^ flow (!^ "," ^^ break 1) (List.map (pp true) es) ^^ rparen)
  | Constructor (x, es) ->
    if es = [] then
      PathName.pp x
    else
      group (
        Pp.open_paren paren ^^
        flow (break 1) (PathName.pp x :: List.map (pp true) es) ^^
        Pp.close_paren paren)
  | Apply (e_f, e_xs) ->
    group (
      Pp.open_paren paren ^^
      flow (break 1) (List.map (pp true) (e_f :: e_xs)) ^^
      Pp.close_paren paren)
  | Function (x, e) ->
    group (flow (break 1) [
      Pp.open_paren paren ^^ !^ "fun"; Name.pp x; !^ "=>";
      pp false e ^^ Pp.close_paren paren])
  | Let (x, e1, e2) ->
    group (flow (break 1) [
      Pp.open_paren paren ^^ !^ "let"; Name.pp x; !^ ":="; pp false e1; !^ "in";
      nest 2 (pp false e2 ^^ Pp.close_paren paren)])
  | LetFun (is_rec, f_name, typ_vars, xs, f_typ, e_f, e) ->
    group (flow (break 1) [
      Pp.open_paren paren ^^ !^ "let";
      (match is_rec with
      | Recursivity.Recursive -> !^ "fix"
      | _ -> empty);
      Name.pp f_name;
      (if typ_vars = [] then empty
      else group (flow (break 1) (
          !^ "{" ::
          List.map Name.pp typ_vars @ [
          !^ ":"; !^ "Type"; !^ "}"])));
      group (flow (break 1) (xs |> List.map (fun (x, x_typ) -> flow (break 1) [
        lparen ^^ Name.pp x; !^ ":"; Type.pp false x_typ ^^ rparen])));
      !^ ":"; Type.pp false f_typ; !^ ":=" ^^ hardline ^^
      pp false e_f; !^ "in" ^^ hardline ^^
      pp false e ^^ Pp.close_paren paren])
  | Match (e, cases) ->
    group (flow (break 1) [
      !^ "match"; pp false e; !^ "with" ^^ hardline ^^
      flow (break 1) (cases |> List.map (fun (p, e) ->
        group (flow (break 1) [!^ "|"; Pattern.pp false p; !^ "=>"; nest 2 (pp false e) ^^ hardline]))) ^^
      !^ "end"])
  | Record fields ->
    group (flow (break 1) [!^ "{|"; flow (!^ ";" ^^ break 1) (fields |> List.map (fun (x, e) ->
      group (flow (break 1) [PathName.pp x; !^ ":="; pp false e]))); !^ "|}"])
  | Field (e, x) -> group (Pp.open_paren paren ^^ PathName.pp x ^/^ pp true e ^^ Pp.close_paren paren)
  | IfThenElse (e1, e2, e3) ->
    group (flow (break 1) [
      !^ "if"; pp false e1; !^ "then" ^^ hardline ^^
      nest 2 (pp false e2) ^^ hardline ^^
      !^ "else" ^^ hardline ^^
      nest 2 (pp false e3)])
  | Return e -> pp paren (Apply (Variable (PathName.of_name [] "ret"), [e]))
  | Bind (e1, x, e2) ->
    group (flow (break 1) [
      Pp.open_paren paren ^^ !^ "let!"; Name.pp x; !^ ":="; pp false e1; !^ "in";
      nest 2 (pp false e2 ^^ Pp.close_paren paren)])