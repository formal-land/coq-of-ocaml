open Monad.Notations

module InductiveVariable = struct
  type t =
    | Error
    | Parameter of Name.t
    | Index of Name.t
    | Unknown
end

module IndParams = struct
  type t = InductiveVariable.t list
end

let get_parameters (typs : IndParams.t) : Name.t list =
  typs |> List.filter_map (function
      | InductiveVariable.Parameter name -> Some name
      | _ -> None)

let rec inductive_variable (typ : Types.type_expr) : InductiveVariable.t Monad.t =
  match typ.Types.desc with
  | Tvar x | Tunivar x ->
    begin match x with
    | None | Some "_" -> return InductiveVariable.Unknown
    | Some x ->
      Name.of_string false x >>= fun x ->
      return (InductiveVariable.Parameter x)
    end
  | Tlink typ | Tsubst typ -> inductive_variable typ
  | Tconstr (typ, _, _) ->
    Path.last typ |> Name.of_string false >>= fun typ ->  return (InductiveVariable.Index typ)
  | _ -> return InductiveVariable.Error

let inductive_variables (typs : Types.type_expr list) : InductiveVariable.t list Monad.t =
  Monad.List.map inductive_variable typs

let filter_params (typs : Types.type_expr list)
  : IndParams.t Monad.t =
  Monad.List.map inductive_variable typs >>= fun typs ->
  typs |> List.filter (function
      | InductiveVariable.Parameter _ -> true
      | _ -> false)
  |> return

  let typ_params_ghost_marked
  (typs : Types.type_expr list) : IndParams.t Monad.t =
  typs |> filter_params

let equal (param1 : InductiveVariable.t) (param2 : InductiveVariable.t) =
  match param1, param2 with
  | Error, Error | Unknown, Unknown -> true
  | Parameter name1, Parameter name2 | Index name1, Index name2 -> Name.equal name1 name2
  | _, _ -> false

let rec merge_typ_params
    (params1 : InductiveVariable.t option list)
    (params2 : InductiveVariable.t option list)
  : InductiveVariable.t option list =
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
  (defined_typ_params : IndParams.t) (return_typ : Types.type_expr option)
  : IndParams.t Monad.t =
  match return_typ with
  | Some { Types.desc = Tconstr (_, typs, _); _ } ->
    Monad.List.map inductive_variable typs
  | _ -> return (defined_typ_params)

let rec adt_parameters
    (defined_typ_params : InductiveVariable.t option list)
    (constructors_return_typ_params : InductiveVariable.t option list list)
  : IndParams.t =
  match constructors_return_typ_params with
  | [] -> List.filter_map (fun x -> x) defined_typ_params
  | return_typ_params :: constructors_return_typ_params ->
    let typ_params = merge_typ_params defined_typ_params return_typ_params in
    adt_parameters typ_params constructors_return_typ_params


let rec gadt_shape'
    (defined_typ_params : InductiveVariable.t option list)
    (constructors_return_typ_params : InductiveVariable.t option list list)
  : InductiveVariable.t option list =
  match constructors_return_typ_params with
  | [] -> defined_typ_params
  | return_typ_params :: constructors_return_typ_params ->
    let typ_params = merge_typ_params defined_typ_params return_typ_params in
    gadt_shape' typ_params constructors_return_typ_params

let gadt_shape
    (defined_typ_params : InductiveVariable.t list)
    (constructors_return_typ_params : InductiveVariable.t list list)
  : InductiveVariable.t option list =
  let defined_typ_params = List.map (function x -> Some x) defined_typ_params in
  let constructors_return_typ_params =
    List.map (function xs ->
        List.map (function x -> Some x) xs)
      constructors_return_typ_params in
  gadt_shape' defined_typ_params constructors_return_typ_params

(** Check if the type is not a GADT. If this is not a GADT, also return a
  prefered list of parameter names for the type variables. It merges the
  names found in the definition of the type name and in the constructors. *)
let check_if_not_gadt
    (defined_typ_params : IndParams.t)
    (constructors_return_typ_params : IndParams.t list)
  : IndParams.t option =
  let defined_typ_params' = List.map (function x -> Some x) defined_typ_params in
  let constructors_return_typ_params =
    List.map (function xs ->
        List.map (function x -> Some x) xs)
      constructors_return_typ_params in
  let typ_params = adt_parameters defined_typ_params' constructors_return_typ_params in
      if typ_params <> defined_typ_params
      then Some typ_params
      else None
