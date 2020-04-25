open Monad.Notations

module TypeVariable = struct
  type t =
    | Error
    | Known of Name.t
    | Unknown
end

module TypParams = struct
  type t = Name.t option list
end

let rec named_typ_param (typ : Types.type_expr) : TypeVariable.t Monad.t =
  match typ.Types.desc with
  | Tvar x | Tunivar x ->
    begin match x with
    | None | Some "_" -> return TypeVariable.Unknown
    | Some x ->
      Name.of_string false x >>= fun x ->
      return (TypeVariable.Known x)
    end
  | Tlink typ | Tsubst typ -> named_typ_param typ
  | _ -> return TypeVariable.Error

let named_typ_params_expecting_anything (typs : Types.type_expr list)
  : TypParams.t option Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  return (
    typs |>
    List.map (function
      | TypeVariable.Error -> None
      | Known name -> Some (Some name)
      | Unknown -> Some None
    ) |>
    Util.Option.all
  )

let named_typ_params_expecting_variables (typs : Types.type_expr list)
  : TypParams.t Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  typs |> Monad.List.map (function
    | TypeVariable.Error ->
      raise
        None
        Unexpected
        "Expected a list of named or unspecified '_' type variables"
    | Known name -> return (Some name)
    | Unknown -> return None
  )

let named_typ_params_expecting_variables_or_ignored
  (typs : Types.type_expr list) : TypParams.t Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  return (typs |> List.map (function
    | TypeVariable.Error -> None
    | Known name -> Some name
    | Unknown -> None
  ))

let named_typ_params_with_unknowns (typ_params : TypParams.t)
  : Name.t list Monad.t =
  typ_params |> Monad.List.map (function
    | Some typ_param -> return typ_param
    | None -> Name.of_string false "_"
  )

let named_typ_params_without_unknowns (typ_params : TypParams.t) : Name.t list =
  typ_params |> Util.List.filter_map (function
    | Some typ_param -> Some typ_param
    | None -> None
  )

let rec merge_typ_params (params1 : TypParams.t) (params2 : TypParams.t)
  : TypParams.t option =
  match (params1, params2) with
  | ([], []) -> Some []
  | (_ :: _, []) | ([], _ :: _) -> None
  | (param1 :: params1, param2 :: params2) ->
    Util.Option.bind (merge_typ_params params1 params2) (fun params ->
    match (param1, param2) with
    | (Some param1, Some param2) ->
      if Name.equal param1 param2 then
        Some (Some param1 :: params)
      else
        None
    | (Some param, None) | (None, Some param) -> Some (Some param :: params)
    | (None, None) -> Some (None :: params))

(** Get the parameters of the return type of a constructor if the parameters are
    only variables. Defaults to the parameters of the defined type itself, in
    case of a non-GADT type. *)
let get_return_typ_params
  (defined_typ_params : TypParams.t) (return_typ : Types.type_expr option)
  : TypParams.t option Monad.t =
  match return_typ with
  | Some { Types.desc = Tconstr (_, typs, _); _ } ->
    named_typ_params_expecting_anything typs
  | _ -> return (Some (defined_typ_params))

(** Check if the type is not a GADT. If this is not a GADT, also return a
  prefered list of parameter names for the type variables. It merges the
  names found in the definition of the type name and in the constructors. *)
let rec check_if_not_gadt
  (defined_typ_params : TypParams.t)
  (constructors_return_typ_params : TypParams.t option list)
  : TypParams.t option =
  match constructors_return_typ_params with
  | [] -> Some defined_typ_params
  | return_typ_params :: constructors_return_typ_params ->
    begin match return_typ_params with
    | None -> None
    | Some return_typ_params ->
      let are_variables_different =
        let non_null_variables =
          Util.List.filter_map (fun x -> x) return_typ_params in
        List.length non_null_variables <>
          Name.Set.cardinal (Name.Set.of_list non_null_variables) in
      if are_variables_different then
        None
      else
        Util.Option.bind
          (merge_typ_params defined_typ_params return_typ_params)
          (fun defined_typ_params ->
            check_if_not_gadt defined_typ_params constructors_return_typ_params
          )
    end
