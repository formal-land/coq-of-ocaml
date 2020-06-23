open Monad.Notations

module AdtVariable = struct
  type t =
    | Error
    | Parameter of Name.t
    | Index of Name.t
    | Unknown

  let rec of_ocaml (typ : Types.type_expr) : t Monad.t =
    match typ.Types.desc with
    | Tvar x | Tunivar x ->
      begin match x with
        | None | Some "_" -> return Unknown
        (* | Some "_" -> *)
          (* Name.of_string false "unit" >>= fun x -> *)
          (* return (Parameter x) *)
        | Some x ->
          Name.of_string false x >>= fun x ->
          return (Parameter x)
      end
    | Tlink typ | Tsubst typ -> of_ocaml typ
    | Tconstr (typ, _, _) ->
      Path.last typ |> Name.of_string false >>= fun typ ->  return (Index typ)
    | _ -> return Error

end

type t = AdtVariable.t list

let get_name : AdtVariable.t -> Name.t option = function
  | AdtVariable.Parameter name | Index name -> Some name
  | _ -> None

let get_parameters (typs : t) : Name.t list =
  typs |> List.filter_map (function
      | AdtVariable.Parameter name -> Some name
      | Unknown -> Some (Make "unit")
      | _ -> None)

let of_ocaml : Types.type_expr list -> t Monad.t =
  Monad.List.map AdtVariable.of_ocaml

let filter_params (typs : Types.type_expr list)
  : t Monad.t =
  of_ocaml typs >>= fun typs ->
  typs |> Monad.List.filter (function
      | AdtVariable.Parameter _ -> return true
      | _ -> return false)

let typ_params_ghost_marked
    (typs : Types.type_expr list)
  : t Monad.t =
  typs |> filter_params

let equal
    (param1 : AdtVariable.t)
    (param2 : AdtVariable.t)
  : bool =
  match param1, param2 with
  | Error, Error | Unknown, Unknown -> true
  | Parameter name1, Parameter name2 | Index name1, Index name2 ->
    Name.equal name1 name2
  | _, _ -> false

let rec merge_typ_params
    (params1 : AdtVariable.t option list)
    (params2 : AdtVariable.t option list)
  : AdtVariable.t option list =
  match (params1, params2) with
  | ([], []) -> []
  | (_ :: _, []) | ([], _ :: _) -> []
  | (param1 :: params1, param2 :: params2) ->
    let params = merge_typ_params params1 params2 in
    begin match (param1, param2) with
      | (Some param1, Some param2) ->
        if equal param1 param2 then
          Some param1 :: params
        else
          None :: params
      | (Some _, None) | (None, Some _) -> None :: params
      | (None, None) -> None :: params
    end

(** Get the parameters of the return type of a constructor if the parameters are
    only variables. Defaults to the parameters of the defined type itself, in
    case of a non-GADT type. *)
let get_return_typ_params
    (defined_typ_params : t)
    (return_typ : Types.type_expr option)
  : t Monad.t =
  match return_typ with
  | Some { Types.desc = Tconstr (_, typs, _); _ } ->
    of_ocaml typs
  | _ -> return (defined_typ_params)

let rec adt_parameters
    (defined_typ_params : AdtVariable.t option list)
    (constructors_return_typ_params : AdtVariable.t option list list)
  : t =
  match constructors_return_typ_params with
  | [] -> List.filter_map (fun x -> x) defined_typ_params
  | return_typ_params :: constructors_return_typ_params ->
    let typ_params = merge_typ_params defined_typ_params return_typ_params in
    adt_parameters typ_params constructors_return_typ_params

let gadt_shape
    (defined_typ_params : AdtVariable.t list)
    (constructors_return_typ_params : AdtVariable.t list list)
  : AdtVariable.t option list =
  let defined_typ_params = List.map (function x -> Some x) defined_typ_params in
  let constructors_return_typ_params =
    List.map (function xs ->
        List.map (function x -> Some x) xs)
      constructors_return_typ_params in
  List.fold_left merge_typ_params defined_typ_params constructors_return_typ_params

(** Check if the type is not a GADT. If this is not a GADT, also return a
  prefered list of parameter names for the type variables. It merges the
  names found in the definition of the type name and in the constructors. *)
let check_if_not_gadt
    (defined_typ_params : t)
    (constructors_return_typ_params : t list)
  : t option =
  let defined_typ_params' = List.map (function x -> Some x) defined_typ_params in
  let constructors_return_typ_params =
    List.map (function xs ->
        List.map (function x -> Some x) xs)
      constructors_return_typ_params in
  let typ_params = adt_parameters defined_typ_params' constructors_return_typ_params in
      if typ_params <> defined_typ_params
      then Some typ_params
      else None
