type t =
  | Variable of Name.t
  | Arrow of t * t
  | Tuple of t list
  | Apply of PathName.t * t list

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
