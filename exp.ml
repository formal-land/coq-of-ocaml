type t =
  | Constant of Constant.t
  | Variable of PathName.t
  | Tuple of t list
  | Constructor of PathName.t * t list
  | Apply of t * t list
  | Function of Name.t * t
  | Let of Name.t * t * t

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
  | Texp_tuple es -> Tuple (List.map of_expression es)
  | Texp_construct (path, _, _, es, _) -> Constructor (PathName.of_path path, List.map of_expression es)
  | _ -> failwith "expression not handled"

let rec pp (f : Format.formatter) (paren : bool) (e : t) : unit =
  let open_paren () = if paren then Format.fprintf f "(" in
  let close_paren () = if paren then Format.fprintf f ")" in
  match e with
  | Constant c -> Constant.pp f c
  | Variable x -> PathName.pp f x
  | Tuple es ->
    Format.fprintf f "(";
    (match es with
    | [] -> ()
    | e :: es -> pp f true e; List.iter (fun e -> Format.fprintf f ", ";  pp f true e) es);
    Format.fprintf f ")"
  | Constructor (x, es) ->
    open_paren ();
    PathName.pp f x;
    List.iter (fun e -> Format.fprintf f "@ "; pp f true e) es;
    close_paren ()
  | Apply (e_f, e_xs) ->
    open_paren ();
    pp f true e_f;
    List.iter (fun e_x -> Format.fprintf f "@ "; pp f true e_x) e_xs;
    close_paren ()
  | Function (x, e) ->
    open_paren ();
    Format.fprintf f "fun@ ";
    Name.pp f x;
    Format.fprintf f "@ =>@ ";
    pp f false e;
    close_paren ()
  | Let (x, e1, e2) ->
    open_paren ();
    Format.fprintf f "let@ ";
    Name.pp f x;
    Format.fprintf f "@ :=@ ";
    pp f false e1;
    Format.fprintf f "@ in@\n";
    pp f false e2;
    close_paren ()
