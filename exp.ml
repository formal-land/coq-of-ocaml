type t =
  | Constant of Constant.t
  | Variable of PathName.t
  | Tuple of t list
  | Constructor of PathName.t * t list
  | Apply of t * t list
  | Function of Name.t * t
  | Let of Name.t * t * t
  | Match of t * (Pattern.t * t) list

let rec of_expression (e : Typedtree.expression) : t =
  let open Typedtree in
  match e.exp_desc with
  | Texp_ident (path, _, _) -> Variable (PathName.of_path path)
  | Texp_constant constant -> Constant (Constant.of_constant constant)
  | Texp_let (Asttypes.Nonrecursive, [x, e1], e2) -> Let (Name.of_pattern x, of_expression e1, of_expression e2)
  | Texp_function (_, [x, e], _) -> Function (Name.of_pattern x, of_expression e)
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
  | _ -> failwith "expression not handled"

let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, e) ->
    let (xs, e) = open_function e in
    (x :: xs, e)
  | _ -> ([], e)

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
