(** An expression. *)
open Typedtree
open Types

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

(** Take a function expression and make explicit the list of arguments and the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

(** Import an OCaml expression. *)
let rec of_expression (e : expression) : t =
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
  let x = Name.fresh "match_var" in
  (x, Match (Variable (PathName.of_name [] x), cases))

(** Pretty-print an expression (inside parenthesis if the [paren] flag is set). *)
let rec pp (f : Format.formatter) (paren : bool) (e : t) : unit =
  match e with
  | Constant c -> Constant.pp f c
  | Variable x -> PathName.pp f x
  | Tuple es ->
    Format.fprintf f "(";
    Pp.sep_by es (fun _ -> Format.fprintf f ", ") (fun e -> pp f true e);
    Format.fprintf f ")"
  | Constructor (x, es) ->
    if es = [] then
      PathName.pp f x
    else (
      Pp.open_paren f paren;
      PathName.pp f x;
      Format.fprintf f "@ ";
      Pp.sep_by es (fun _ -> Format.fprintf f "@ ") (fun e -> pp f true e);
      Pp.close_paren f paren)
  | Apply (e_f, e_xs) ->
    Pp.open_paren f paren;
    Pp.sep_by (e_f :: e_xs) (fun _ -> Format.fprintf f "@ ") (fun e -> pp f true e);
    Pp.close_paren f paren
  | Function (x, e) ->
    Pp.open_paren f paren;
    Format.fprintf f "fun@ ";
    Name.pp f x;
    Format.fprintf f "@ =>@ ";
    pp f false e;
    Pp.close_paren f paren
  | Let (x, e1, e2) ->
    Pp.open_paren f paren;
    Format.fprintf f "let@ ";
    Name.pp f x;
    Format.fprintf f "@ :=@ ";
    pp f false e1;
    Format.fprintf f "@ in@\n";
    pp f false e2;
    Pp.close_paren f paren
  | LetFun (is_rec, f_name, typ_vars, xs, f_typ, e_f, e) ->
    Pp.open_paren f paren;
    Format.fprintf f "let@ ";
    if is_rec = Recursivity.Recursive then
      Format.fprintf f "fix@ ";
    Name.pp f f_name;
    if typ_vars <> [] then (
      Format.fprintf f "@ {";
      List.iter (fun x ->
        Name.pp f x;
        Format.fprintf f "@ ")
        typ_vars;
      Format.fprintf f "@ :@ Type}");
    List.iter (fun (x, x_typ) ->
      Format.fprintf f "@ (";
      Name.pp f x;
      Format.fprintf f "@ :@ ";
      Type.pp f false x_typ;
      Format.fprintf f ")")
      xs;
    Format.fprintf f "@ :@ ";
    Type.pp f false f_typ;
    Format.fprintf f "@ :=@\n";
    pp f false e_f;
    Format.fprintf f "@ in@\n";
    pp f false e;
    Pp.close_paren f paren
  | Match (e, cases) ->
    Format.fprintf f "match@ ";
    pp f false e;
    Format.fprintf f "@ with@\n";
    List.iter (fun (p, e) ->
      Format.fprintf f "|@ ";
      Pattern.pp f false p;
      Format.fprintf f "@ =>@ ";
      pp f false e;
      Format.fprintf f "@\n") cases;
    Format.fprintf f "end"
  | Record fields ->
    Format.fprintf f "{|@ ";
    Pp.sep_by fields (fun _ -> Format.fprintf f ";@ ") (fun (x, e) ->
      PathName.pp f x;
      Format.fprintf f "@ :=@ ";
      pp f false e);
    Format.fprintf f "@ |}"
  | Field (e, x) ->
    Pp.open_paren f paren;
    PathName.pp f x;
    Format.fprintf f "@ ";
    pp f true e;
    Pp.close_paren f paren
  | IfThenElse (e1, e2, e3) ->
    Format.fprintf f "if@ ";
    pp f false e1;
    Format.fprintf f "@ then@ ";
    pp f false e2;
    Format.fprintf f "@ else@ ";
    pp f false e3