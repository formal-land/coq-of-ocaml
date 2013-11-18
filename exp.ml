open Typedtree

type t =
  | Constant of Constant.t
  | Variable of PathName.t
  | Tuple of t list
  | Constructor of PathName.t * t list
  | Apply of t * t list
  | Function of Name.t * t
  | Let of Name.t * t * t
  | LetFun of Recursivity.t * Name.t * Name.t list * (Name.t * Type.t) list * Type.t * t * t
  | Match of t * (Pattern.t * t) list
  | Record of (PathName.t * t) list
  | Field of t * PathName.t

let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

let rec of_expression (e : expression) : t =
  match e.exp_desc with
  | Texp_ident (path, _, _) -> Variable (PathName.of_path path)
  | Texp_constant constant -> Constant (Constant.of_constant constant)
  | Texp_let (rec_flag, [{pat_desc = Tpat_var (x, _)}, e1], e2) ->
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
  | Texp_function (_, [{pat_desc = Tpat_var (x, _)}, e], _) -> Function (Name.of_ident x, of_expression e)
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
    let cases = List.map (fun (p, e) -> (Pattern.of_pattern p, of_expression e)) cases in
    Match (e, cases)
  | Texp_tuple es -> Tuple (List.map of_expression es)
  | Texp_construct (path, _, _, es, _) -> Constructor (PathName.of_path path, List.map of_expression es)
  | Texp_record (fields, _) -> Record (List.map (fun (path, _, _, e) -> (PathName.of_path path, of_expression e)) fields)
  | Texp_field (e, path, _, _) -> Field (of_expression e, PathName.of_path path)
  | _ -> failwith "expression not handled"
and open_cases (cases : (pattern * expression) list) : Name.t * t =
  let cases = List.map (fun (pattern, e) -> (Pattern.of_pattern pattern, of_expression e)) cases in
  let x = Name.fresh "match_var" in
  (x, Match (Variable (PathName.of_name x), cases))

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