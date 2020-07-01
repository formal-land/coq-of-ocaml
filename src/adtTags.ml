(* We keep the actual types around for the decode function later on *)
type t = Name.t * Type.t list * AdtConstructors.t

let get_tag_constructor
    (name : Name.t)
    (* (typ : Type.t) *)
    (typ_name : Name.t)
  : Name.t =
  let name = Name.to_string name in
  let typ_name = Name.to_string typ_name in
  (* Name.Make (name ^ "_" ^ (Type.to_string typ) ^ "_tag") *)
  Name.Make (name ^ "_" ^ typ_name ^ "_tag")

let of_typs
    (name : Name.t)
    (typs : Type.t list) : t =
  let typs = typs |> List.sort_uniq Type.compare
  in
  let constructors = typs |> List.fold_left (fun constructors typ ->
      let typ_vars = Type.typ_args_of_typ typ |> Name.Set.elements in
      let typ_name = Name.Make (Type.to_string typ) in
      let constructor_name = get_tag_constructor name typ_name in
      let constructor : AdtConstructors.item = {
        constructor_name;
        param_typs = [];
        res_typ_params = [];
        typ_vars
      } in (constructor :: constructors)) [] in
  (Name.suffix_by_tag name, typs, List.rev constructors)

let tag_typ
    (name : Name.t)
    (typ : Type.t) =
  let free_vars = Type.typ_args_of_typ typ
                  |> Name.Set.elements
                  |> List.map (function name -> Type.Variable name) in
  let type_name = Name.Make (Type.to_string typ) in
  let tag_constructor = get_tag_constructor name type_name in
  Type.Apply (MixedPath.of_name tag_constructor, free_vars)

let rec rename_app
    (name : Name.t)
  : Type.t -> Type.t = function
  | Apply (s, ts) ->
    let ts =
      if s = MixedPath.of_name name
      then ts |> List.map (function typ -> tag_typ name typ)
      else ts in
    Apply (s, ts)
  | Arrow (t1, t2) -> Arrow (rename_app name t1, rename_app name t2)
  | Sum ls ->
    let (s, ts) = List.split ls in
    let ts = List.map (rename_app name) ts in
    Sum (List.combine s ts)
  | Tuple ts -> Tuple (List.map (rename_app name) ts)
  (* Do I need to rename n? *)
  | ForallModule (n, t1,t2) -> ForallModule (n, rename_app name t1, rename_app name t2)
  | ForallTyps (n, t) -> ForallTyps (n, rename_app name t)
  | FunTyps (n, t) -> FunTyps (n, rename_app name t)
  | _ as t -> t


let tag_constructor
    (name : Name.t)
    (constructor : AdtConstructors.item)
    : AdtConstructors.item =
  let { AdtConstructors.res_typ_params; param_typs; _ } = constructor in
  let param_typs = param_typs |> List.map (rename_app name) in
  let res_typ_params = res_typ_params |> List.map (fun typ -> tag_typ name typ) in
  { constructor with res_typ_params; param_typs }


let tag_constructors (name : Name.t)
  : AdtConstructors.t -> AdtConstructors.t =
  List.map (fun item -> tag_constructor name item)
