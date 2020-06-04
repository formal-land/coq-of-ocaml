open Monad.Notations

module TypeVariable = struct
  type t =
    | Error
    | Known of Name.t
    | Unknown
end

module TypParams = struct
  type t = Name.t list
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

let filter_error_params (typs : Types.type_expr list)
  : TypParams.t Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  typs |> List.filter_map (function
      | TypeVariable.Error ->
        None
      | Known name ->
        Some name
      | Unknown ->
        None)
  |> return

let named_typ_params_expecting_variables (typs : Types.type_expr list)
  : TypParams.t Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  typs |> Monad.List.filter_map (function
    | TypeVariable.Error ->
      raise
        None
        Unexpected
        "Expected a list of named or unspecified '_' type variables"
    | Known name -> return (Some name)
    | Unknown -> return None
  )


let typ_params_ghost_marked
  (typs : Types.type_expr list) : Name.t option list Monad.t =
  Monad.List.map named_typ_param typs >>= fun typs ->
  return (typs |> List.map (function
    | TypeVariable.Error -> None
    | Known name -> Some name
    | Unknown -> None
  ))

let rec merge_typ_params (params1 : TypParams.t) (params2 : TypParams.t)
  : TypParams.t =
  match (params1, params2) with
  | ([], []) -> []
  | (_ :: _ as xs, []) | ([], (_ :: _ as xs)) -> xs
  | (param1 :: params1, param2 :: params2) ->
    let params = merge_typ_params params1 params2 in
    if Name.equal param1 param2 then
      param1 :: params
    else
      params

(** Get the parameters of the return type of a constructor if the parameters are
    only variables. Defaults to the parameters of the defined type itself, in
    case of a non-GADT type. *)
let get_return_typ_params
  (defined_typ_params : TypParams.t) (return_typ : Types.type_expr option)
  : TypParams.t Monad.t =
  match return_typ with
  | Some { Types.desc = Tconstr (_, typs, _); _ } ->
    filter_error_params typs
  | _ -> return (defined_typ_params)

let print_typParams (tys : TypParams.t) : unit =
  let ts = tys |> List.map (function ty -> Name.to_string ty )
           |> String.concat ", " in
  print_string ("Ty Params : " ^ ts ^ "\n")

let rec adt_parameters
  (defined_typ_params : TypParams.t)
  (constructors_return_typ_params : TypParams.t list)
  : TypParams.t =
  match constructors_return_typ_params with
  | [] -> defined_typ_params
  | return_typ_params :: constructors_return_typ_params ->
    let typ_params = merge_typ_params defined_typ_params return_typ_params in
    adt_parameters typ_params constructors_return_typ_params

(** Check if the type is not a GADT. If this is not a GADT, also return a
  prefered list of parameter names for the type variables. It merges the
  names found in the definition of the type name and in the constructors. *)
let check_if_not_gadt
    (defined_typ_params : TypParams.t)
    (constructors_return_typ_params : TypParams.t list)
  : TypParams.t option =
  let typ_params = adt_parameters defined_typ_params constructors_return_typ_params in
      if typ_params <> defined_typ_params
      then Some typ_params
      else None
