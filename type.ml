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

let rec pp (f : Format.formatter) (typ : t) : unit =
  match typ with
  | Variable x -> Name.pp f x
  | Arrow (typ_x, typ_y) ->
    Format.fprintf f "(";
    pp f typ_x;
    Format.fprintf f "@ ->@ ";
    pp f typ_y;
    Format.fprintf f ")"
  | Tuple typs ->
    (match typs with
    | [] -> Format.fprintf f "unit"
    | typ :: typss ->
      Format.fprintf f "(";
      pp f typ;
      List.iter (fun typ -> Format.fprintf f "@ *@ "; pp f typ) (List.tl typs);
      Format.fprintf f ")")
  | Apply (constr, typs) ->
    Format.fprintf f "(";
    PathName.pp f constr;
    List.iter (fun typ -> Format.fprintf f "@ "; pp f typ) typs;
    Format.fprintf f ")"
