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
        | None -> return Unknown
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

