open Types

type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of PathName.t * t list

let rec of_type_expr (typ : Types.type_expr) : t =
  match typ.desc with
  | Tvar None -> Variable (Printf.sprintf "A%d" typ.id)
  | Tvar (Some x) -> Variable x
  | Tarrow (_, typ_x, typ_y, _) -> Arrow (of_type_expr typ_x, of_type_expr typ_y)
  | Ttuple typs -> Tuple (List.map of_type_expr typs)
  | Tconstr (path, typs, _) -> Apply (PathName.of_path path, List.map of_type_expr typs)
  | Tlink typ -> of_type_expr typ
  | Tpoly (typ, []) -> of_type_expr typ
  | _ -> failwith "type not handled"

let rec free_vars (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ_x, typ_y) -> Name.Set.union (free_vars typ_x) (free_vars typ_y)
  | Tuple typs | Apply (_, typs) -> List.fold_left (fun s typ -> Name.Set.union s (free_vars typ)) Name.Set.empty typs

(** In a function's type, extract the list of arguments' types (up to n elements) and the body's type  *)
let rec open_function (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ_x, typ_y) ->
      let (typs, typ) = open_function typ_y (n - 1) in
      (typ_x :: typs, typ)
    | _ -> ([], typ)

(** Replace a variable name by another. *)
let rec substitute_variable (typ : t) (x : Name.t) (x' : Name.t) : t =
  match typ with
  | Variable y -> if x = y then Variable x' else typ
  | Arrow (typ1, typ2) -> Arrow (substitute_variable typ1 x x', substitute_variable typ2 x x')
  | Tuple typs -> Tuple (List.map (fun typ -> substitute_variable typ x x') typs)
  | Apply (path, typs) -> Apply (path, List.map (fun typ -> substitute_variable typ x x') typs)

let rec pp (f : Format.formatter) (paren : bool) (typ : t) : unit =
  match typ with
  | Variable x -> Name.pp f x
  | Arrow (typ_x, typ_y) ->
    Pp.open_paren f paren;
    pp f true typ_x;
    Format.fprintf f "@ ->@ ";
    pp f false typ_y;
    Pp.close_paren f paren
  | Tuple typs ->
    (match typs with
    | [] -> Format.fprintf f "unit"
    | _ ->
      Pp.open_paren f paren;
      Pp.sep_by typs (fun _ -> Format.fprintf f "@ *@ ") (fun typ -> pp f true typ);
      Pp.close_paren f paren)
  | Apply (constr, typs) ->
    if typs <> [] then Pp.open_paren f paren;
    PathName.pp f constr;
    List.iter (fun typ -> Format.fprintf f "@ "; pp f true typ) typs;
    if typs <> [] then Pp.close_paren f paren
