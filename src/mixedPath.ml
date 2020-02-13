(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open SmartPrint
open Monad.Notations

(** [Access] corresponds to projections from first-class modules. *)
type t =
  | Access of PathName.t * PathName.t list * bool
  | PathName of PathName.t

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

let get_signature_path (path : Path.t) : Path.t option Monad.t =
  get_env >>= fun env ->
  match Env.find_module path env with
  | module_declaration ->
    let { Types.md_type; _ } = module_declaration in
    IsFirstClassModule.is_module_typ_first_class md_type >>= fun is_first_class ->
    begin match is_first_class with
    | IsFirstClassModule.Found signature_path -> return (Some signature_path)
    | IsFirstClassModule.Not_found _ -> return None
    end
  | exception _ -> return None

let rec of_path_aux (path : Path.t)
  : (Path.t * (Path.t * string) list * Path.t option) Monad.t =
  get_signature_path path >>= fun signature_path ->
  begin match path with
  | Papply _ -> failwith "Unexpected path application"
  | Pdot (path', field_string, _) ->
    of_path_aux path' >>= fun (namespace_path, fields, signature_path) ->
    begin match signature_path with
    | Some signature_path ->
      return (
        namespace_path,
        (signature_path, field_string) :: fields
      )
    | None ->
      (* The sub-module of a first-class module is a first-class module too. *)
      return (path, [])
    end
  | Pident _ -> return (path, [])
  end >>= fun (path, fields) ->
  return (path, fields, signature_path)

let get_module_path_location (path : Path.t) (env : Env.t) : Location.t option =
  match Env.find_module path env with
  | { Types.md_loc; _ } -> Some md_loc
  | exception _ -> None

(** If the module was declared in the current unbundled signature definition. *)
let is_module_path_local (path : Path.t) : bool Monad.t =
  get_scoping_env false >>= fun outer_scoping_env ->
  get_scoping_env true >>= fun inner_scoping_env ->
  get_env >>= fun env ->
  match get_module_path_location path env with
  | Some location ->
    begin match (outer_scoping_env, inner_scoping_env) with
    | (None, None) -> return false
    | (Some outer_scoping_env, None) ->
      let outer_location = get_module_path_location path outer_scoping_env in
      begin match outer_location with
      | Some outer_location -> return (outer_location <> location)
      | None -> return true
      end
    | (None, Some _) ->
      (* The inner environment is supposed to be there only in cases where there
         is an outer environment too. *)
      assert false
    | (Some outer_scoping_env, Some inner_scoping_env) ->
      let outer_location = get_module_path_location path outer_scoping_env in
      let inner_location = get_module_path_location path inner_scoping_env in
      begin match (outer_location, inner_location) with
      | (Some outer_location, Some inner_location) ->
        return (outer_location <> inner_location && inner_location = location)
      | (_, None) -> return false
      | (None, Some inner_location) -> return (inner_location = location)
      end
    end
  | None ->
    (* The [path] is supposed to be in the current environment. *)
    assert false

(** The current environment must include the potential first-class module
    signature definition of the corresponding projection in the [path]. *)
let of_path
  (is_value : bool)
  (path : Path.t)
  (long_ident : Longident.t option)
  : t Monad.t =
  of_path_aux path >>= fun (base_path, fields, signature_path) ->
  match (fields, signature_path) with
  | ([], None) ->
    let path_name = PathName.of_path_without_convert is_value base_path in
    begin match PathName.try_convert path_name with
    | None ->
      begin match long_ident with
      | None -> return (PathName path_name)
      | Some long_ident -> return (PathName (PathName.of_long_ident is_value long_ident))
      end
    | Some path_name -> return (PathName path_name)
    end
  | _ ->
    is_module_path_local base_path >>= fun is_local ->
    let base_path_name = PathName.of_path_with_convert is_value base_path in
    return (Access (
      base_path_name,
      fields |> List.map (fun (signature_path, field_string) ->
        let field_name = Name.of_string is_value field_string in
        PathName.of_path_and_name_with_convert signature_path field_name
      ) |> List.rev,
      is_local
    ))

let to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, fields, is_local) ->
    let path = PathName.to_coq path in
    let path =
      if is_local then
        path
      else
        parens (!^ "|" ^-^ path ^-^ !^ "|") in
    let fields =
      fields |> List.map (fun field -> parens (PathName.to_coq field)) in
    separate (!^ ".") (path :: fields)
  | PathName path_name -> PathName.to_coq path_name
