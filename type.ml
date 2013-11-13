type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of PathName.t * t list

(** In a function's type, extract the list of arguments' types and the body's type *)
let rec open_function (typ : t) : t list * t =
  match typ with
  | Arrow (typ_x, typ_y) ->
    let (typs, typ) = open_function typ_y in
    (typ_x :: typs, typ)
  | _ -> ([], typ)

let rec pp (f : Format.formatter) (paren : bool) (typ : t) : unit =
  let open_paren () = if paren then Format.fprintf f "(" in
  let close_paren () = if paren then Format.fprintf f ")" in
  match typ with
  | Variable x -> Name.pp f x
  | Arrow (typ_x, typ_y) ->
    open_paren ();
    pp f true typ_x;
    Format.fprintf f "@ ->@ ";
    pp f false typ_y;
    close_paren ()
  | Tuple typs ->
    (match typs with
    | [] -> Format.fprintf f "unit"
    | typ :: typss ->
      open_paren ();
      pp f true typ;
      List.iter (fun typ -> Format.fprintf f "@ *@ "; pp f true typ) (List.tl typs);
      close_paren ())
  | Apply (constr, typs) ->
    if typs <> [] then open_paren ();
    PathName.pp f constr;
    List.iter (fun typ -> Format.fprintf f "@ "; pp f true typ) typs;
    if typs <> [] then close_paren ()
