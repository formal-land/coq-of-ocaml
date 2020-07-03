open Monad.Notations

(* We keep the actual types around for the decode function later on *)
type t = Name.t * Type.t list * AdtConstructors.t

let get_tag_constructor
    (name : Name.t)
    (* (typ : Type.t) *)
    (typ_name : Name.t)
  : Name.t =
  let name = Name.to_string name in
  let typ_name = Name.to_string typ_name in
  Name.Make (name ^ "_" ^ typ_name ^ "_tag")


let of_typs
    (name : Name.t)
    (typs : Type.t list) : t * Name.t Type.Map.t =
  let typs = typs |> List.sort_uniq compare |> List.sort_uniq Type.compare in
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
  let constructors = List.rev constructors in
  let tags = (Name.suffix_by_tag name, typs, List.rev constructors) in
  let mapping = List.map2 (fun typ { AdtConstructors.constructor_name; _ } -> (typ, constructor_name)) typs constructors
              |> List.to_seq in
  let mapping = Type.Map.add_seq mapping Type.Map.empty in
  (tags, mapping)

let tag_typ
    (name : Name.t)
    (typ : Type.t)
  : Type.t =
  let free_vars = Type.typ_args_of_typ typ
                  |> Name.Set.elements
                  |> List.map (function name -> Type.Variable name) in
  let type_name = Name.Make (Type.to_string typ) in
  let tag_constructor = get_tag_constructor name type_name in
  Type.Apply (MixedPath.of_name tag_constructor, free_vars)

let rec tag_all_typ
  : Type.t -> Type.t = function
  | Type.Apply (mname, ts) as t ->
    let builtins = List.map (fun x -> MixedPath.of_name @@ Name.of_string_raw x) ["list"; "option"] in
    if not @@ List.for_all (fun builtin -> mname = builtin) builtins
    then t
    else Type.Apply (mname, List.map tag_all_typ ts)
  | _ as t -> t

let rec tag_args_of
    (name : Name.t)
  : Type.t -> Type.t = function
  | Apply (s, ts) ->
    let ts =
      if s = MixedPath.of_name name
      then ts |> List.map @@ tag_typ name
      else ts |> List.map @@ tag_args_of name in
    Apply (s, ts)
  | Arrow (t1, t2) -> Arrow (tag_args_of name t1, tag_args_of name t2)
  | Sum ls ->
    let (s, ts) = List.split ls in
    let ts = List.map (tag_args_of name) ts in
    Sum (List.combine s ts)
  | Tuple ts -> Tuple (List.map (tag_args_of name) ts)
  (* Do I need to rename n? *)
  | ForallModule (n, t1,t2) -> ForallModule (n, tag_args_of name t1, tag_args_of name t2)
  | ForallTyps (n, t) -> ForallTyps (n, tag_args_of name t)
  | FunTyps (n, t) -> FunTyps (n, tag_args_of name t)
  | _ as t -> t


let tag_constructor
    (name : Name.t)
    (constructor : AdtConstructors.item)
    : AdtConstructors.item =
  let { AdtConstructors.res_typ_params; param_typs; _ } = constructor in
  let param_typs = param_typs |> List.map (tag_args_of name) in
  let res_typ_params = res_typ_params |> List.map (fun typ -> tag_typ name typ) in
  { constructor with res_typ_params; param_typs }

let tag_constructors (name : Name.t)
  : AdtConstructors.t -> AdtConstructors.t =
  List.map (fun item -> tag_constructor name item)

let rec get_application_of
    (name : Name.t)
  : Type.t -> Type.t list = function
  | Type.Apply (s, ts) ->
    if s = MixedPath.of_name name
    then ts
    else []
  | _ -> []

let get_index_typs
  (name : Name.t)
  (constructors : AdtConstructors.t list)
  : Type.t list =
  let res_typ_params = constructors |> List.flatten
                       |> List.map (fun { AdtConstructors.res_typ_params; _} -> res_typ_params )
                       |> List.flatten in
  let param_typs = constructors |> List.flatten
                   |> List.map (fun { AdtConstructors.param_typs; _ } ->
                       List.map (get_application_of name) param_typs)
                   |> List.flatten
                   |> List.flatten in
  Type.Variable (Name.of_string_raw "a") :: res_typ_params @ param_typs

let rec get_args_of
    (path : Path.t)
  : Types.type_expr -> Types.type_expr list = function
  |  { desc = Tconstr (p, exprs, _); _ }->
    if p = path
    then exprs
    else []
  | _ -> []

let rec get_tag_of
    (path : Path.t)
  : Name.t Type.Map.t Monad.t =
  get_env >>= fun env ->
  let name = Name.of_string_raw @@ Path.last path in
  begin match Env.find_type path env with
    | { type_kind = Type_variant constructors ; _ } ->
      let typs = constructors |> List.map (fun { Types.cd_res; _ } -> cd_res) |> List.filter_map (fun x -> x) in
      (* TODO: Cstr_record *)
      let args = constructors
                 |> List.map (fun { Types.cd_args; _ } ->
                     match cd_args with
                     | Cstr_tuple typs -> typs
                     | _ -> [])
                 |> List.flatten
                 |> List.map (get_args_of path)
                 |> List.flatten in
      let* (typs, _, _) = Type.of_typs_exprs true Name.Map.empty (typs @ args) in
      let (_, mapping) = of_typs name typs in
      return mapping
    | _ -> raise Type.Map.empty Error.Category.Unexpected "Could not find type declaration"
  end
