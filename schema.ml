type t = {
  variables : Name.t list;
  typ : Type.t}

let of_type_expr (typ : Types.type_expr) : t =
  let rec aux typ : Name.Set.t * Type.t =
    match typ.Types.desc with
    | Types.Tvar None ->
      let x = Printf.sprintf "A%d" typ.Types.id in
      (Name.Set.singleton x, Type.Variable x)
    | Types.Tarrow (_, typ_x, typ_y, _) ->
      let (s_x, typ_x) = aux typ_x in
      let (s_y, typ_y) = aux typ_y in
      (Name.Set.union s_x s_y, Type.Arrow (typ_x, typ_y))
    | Types.Ttuple typs ->
      let (ss, typs) = List.split (List.map aux typs) in
      (List.fold_left Name.Set.union Name.Set.empty ss, Type.Tuple typs)
    | Types.Tconstr (path, typs, _) ->
      let (ss, typs) = List.split (List.map aux typs) in
      (List.fold_left Name.Set.union Name.Set.empty ss, Type.Apply (PathName.of_path path, typs))
    | Types.Tlink typ -> aux typ
    | _ -> failwith "type not handled" in
  let (s, typ) = aux typ in
  { variables = Name.Set.elements s; typ = typ }

let of_expression (e : Typedtree.expression) : t =
  of_type_expr e.Typedtree.exp_type

let pp (f : Format.formatter) (schema : t) : unit =
  (match schema.variables with
  | [] -> ()
  | xs ->
    Format.fprintf f "forall@ (";
    List.iter (fun x -> Name.pp f x; Format.fprintf f "@ ") xs;
    Format.fprintf f ":@ Type),@ ");
  Type.pp f schema.typ
