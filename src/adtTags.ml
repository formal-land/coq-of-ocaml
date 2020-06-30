(* We keep the actual types around for the decode function later on *)
type t = Name.t * Type.t list * AdtConstructors.t

let get_tag_constructor
    (name : Name.t)
    (typ : Type.t)
  : Name.t =
  let name = Name.to_string name in
  Name.Make (name ^ "_" ^ (Type.to_string typ) ^ "_tag")

let of_typs
    (name : Name.t)
    (typs : Type.t list) : t =
  let typs = typs |> List.sort_uniq compare in
  let constructors = typs |> List.fold_left (fun constructors typ ->
      let typ_vars = Type.typ_args_of_typ typ |> Name.Set.elements in
      let constructor_name = get_tag_constructor name typ in
      let constructor : AdtConstructors.item = {
        constructor_name;
        param_typs = [];
        res_typ_params = [];
        typ_vars
      } in (constructor :: constructors)) [] in
  (Name.suffix_by_tag name, typs, List.rev constructors)

let tag_constructor
    (name : Name.t)
    (constructor : AdtConstructors.item)
    : AdtConstructors.item =
  let { AdtConstructors.res_typ_params; typ_vars; _ } = constructor in
  let typ_vars = typ_vars |> List.map (fun typ -> Type.Variable typ) in
  let res_typ_params = res_typ_params |> List.map
                         (fun res_typ_param -> get_tag_constructor name res_typ_param)
                       |> List.map (fun x -> Type.Apply ((MixedPath.of_name x), typ_vars)) in
  { constructor with res_typ_params }

let tag_constructors (name : Name.t)
  : AdtConstructors.t -> AdtConstructors.t =
  List.map (fun item -> tag_constructor name item)
