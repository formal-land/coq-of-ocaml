(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open SmartPrint
open Monad.Notations

let path_to_string_list p =
  let open Path in
  let rec aux acc = function
    | Pident id -> Ident.name id :: acc
    | Pdot (p, str) -> aux (str :: acc) p
    | _ -> assert false
  in
  aux [] p 

(** [Access] corresponds to projections from first-class modules. *)
type t =
  | Access of PathName.t * PathName.t list
  | PathName of PathName.t

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

let dec_name : t =
  PathName (Name.decode_vtag |> PathName.of_name [])

let projT1 : t =
  of_name (Name.of_string_raw "projT1")

let prim_proj_fst : t =
  PathName PathName.prim_proj_fst

let prim_proj_snd : t =
  PathName PathName.prim_proj_snd

let is_constr_tag : t -> bool = function
  | Access _ -> false
  | PathName {base; _} -> Name.equal base Name.constr_tag

let get_signature_path (path : Path.t) : Path.t option Monad.t =
  let* env = get_env in
  match Env.find_module path env with
  | module_declaration ->
    let { Types.md_type; _ } = module_declaration in
    let* is_first_class =
      IsFirstClassModule.is_module_typ_first_class md_type (Some path) in
    begin match is_first_class with
    | IsFirstClassModule.Found signature_path -> return (Some signature_path)
    | IsFirstClassModule.Not_found _ -> return None
    end
  | exception _ -> return None

module SignedPath = struct
  type t = {
    path : Path.t;
    signature_path : Path.t option;
  }

  let get (path : Path.t) : t Monad.t =
    let* signature_path = get_signature_path path in
    return { path; signature_path }
end

module RawDecomposedPath = struct
  type t = SignedPath.t * (SignedPath.t * string) list

  let rec get_rev (path : Path.t) : t Monad.t =
    let* signed_path = SignedPath.get path in
    match path with
    | Papply _ -> failwith "Unexpected functor path application"
    | Pident _ -> return (signed_path, [])
    | Pdot (path', field) ->
      let* (start_path, fields) = get_rev path' in
      return (start_path, (signed_path, field) :: fields)
end

module DecomposedPath = struct
  type t =
    | WithField of SignedPath.t * string * t
    | Final of SignedPath.t

  let rec get_of_raw_decomposed_path_rev
    (raw_decomposed_path_rev : RawDecomposedPath.t)
    (decomposed_path : SignedPath.t -> t)
    : t =
    let (start_path, fields) = raw_decomposed_path_rev in
    match fields with
    | [] -> decomposed_path start_path
    | (signed_path, field) :: fields ->
      get_of_raw_decomposed_path_rev
        (start_path, fields)
        (fun next_path ->
          WithField (next_path, field, decomposed_path signed_path)
        )

  let get (path : Path.t) : t Monad.t =
    let* raw_decomposed_path_rev = RawDecomposedPath.get_rev path in
    return (get_of_raw_decomposed_path_rev
      raw_decomposed_path_rev
      (fun next_path -> Final next_path))
end

module FlattenedDecomposedPath = struct
  type t =
    | WithField of Path.t * Path.t * string list * t
    | Final of SignedPath.t

  let rec get
    (decomposed_path : DecomposedPath.t)
    (current_signed_path : (Path.t * Path.t * string list) option)
    : t =
    match (decomposed_path, current_signed_path) with
    | (
        WithField ({ path; signature_path }, field, decomposed_path),
        None
      ) ->
      begin match signature_path with
      | None ->
        get decomposed_path current_signed_path
      | Some signature_path ->
        let current_signed_path = Some (path, signature_path, [field]) in
        get decomposed_path current_signed_path
      end
    | (
        WithField ({ path; signature_path }, field, decomposed_path),
        Some (current_path, current_signature_path, current_fields)
      ) ->
      begin match signature_path with
      | None ->
        let current_signed_path =
          Some (
            current_path, current_signature_path, current_fields @ [field]
          ) in
        get decomposed_path current_signed_path
      | Some signature_path ->
        let current_signed_path = Some (path, signature_path, [field]) in
        WithField (
          current_path, current_signature_path, current_fields,
          get decomposed_path current_signed_path
        )
      end
    | (
        Final signed_path,
        None
      ) -> Final signed_path
    | (
        Final signed_path,
        Some (current_path, current_signature_path, current_fields)
      ) ->
      WithField (
        current_path, current_signature_path, current_fields,
        Final signed_path
      )
end

let rec of_path_aux (flattened_decomposed_path : FlattenedDecomposedPath.t)
  : Path.t * (Path.t * string list) list * Path.t option =
  match flattened_decomposed_path with
  | WithField (path, signature_path, fields, flattened_decomposed_path) ->
    let (_, fields', _) = of_path_aux flattened_decomposed_path in
    (path, (signature_path, fields) :: fields', Some signature_path)
  | Final { path; signature_path } -> (path, [], signature_path)

(** If the module was declared in the current unbundled signature definition. *)
let is_module_path_local (path : Path.t) : bool Monad.t =
  let* env = get_env in
  (* Some paths may not exist, for example for the type of a record field in an
     algebraic type. *)
  let does_exist =
    match Env.find_module path env with
    | _ -> true
    | exception _ -> false in
  let* env_stack = get_env_stack in
  let envs_without_path = env_stack |> List.filter (fun env ->
    match Env.find_module path env with
    | _ -> false
    | exception _ -> true
  ) in
  return (does_exist && List.length envs_without_path mod 2 = 1)

(** In case the base path is local, we need to make a special transformation.
    Indeed, unless if the path is a single name, this means that we access to a
    sub-module with an anonmous signature which has been flattened. *)
let get_local_base_path (is_value : bool) (path : Path.t)
  : PathName.t option Monad.t =
  match path with
  | Papply _ -> failwith "Unexpected functor path application"
  | Pident _ -> return None
  | Pdot (path', _) ->
    let* is_local = is_module_path_local path' in
    if is_local then
      let name_string = String.concat "_" (path_to_string_list path) in
      let* name = Name.of_string is_value name_string in
      return (Some (PathName.of_name [] name))
    else
      return None

(** The current environment must include the potential first-class module
    signature definition of the corresponding projection in the [path]. *)
let of_path (is_value : bool) (path : Path.t) : t Monad.t =
  let* decomposed_path = DecomposedPath.get path in
  let flattened_decomposed_path =
    FlattenedDecomposedPath.get decomposed_path None in
  let (base_path, fields, signature_path) =
    of_path_aux flattened_decomposed_path in
  let fields = List.rev fields in
  let* local_base_path = get_local_base_path is_value base_path in
  match (fields, signature_path) with
  | ([], None) ->
    begin match local_base_path with
    | None ->
      let* path_name = PathName.of_path_without_convert is_value base_path in
      let* conversion = PathName.try_convert path_name in
      begin match conversion with
      | None -> return (PathName path_name)
      | Some path_name -> return (PathName path_name)
      end
    | Some local_base_path -> return (PathName local_base_path)
    end
  | _ ->
    let* base_path_name =
      match local_base_path with
      | None -> PathName.of_path_with_convert is_value base_path
      | Some local_base_path -> return local_base_path in
    let* fields =
      fields |> Monad.List.map (fun (signature_path, fields) ->
        let field = String.concat "_" fields in
        let* field_name = Name.of_string is_value field in
        PathName.of_path_and_name_with_convert signature_path field_name
      ) in
    return (Access (base_path_name, List.rev fields))

let is_native_type (path : t) : bool =
  match path with
  | Access _ -> false
  | PathName { base; _ } -> List.mem (Name.to_string base) Name.native_type_constructors

let to_string (mixed_path : t) : string =
  match mixed_path with
  | Access (path, fields) ->
    let path = PathName.to_string path in
    let fields =
      fields |> List.map (fun field -> "(" ^ PathName.to_string field ^ ")") in
    String.concat "." (path :: fields)
  | PathName path_name -> PathName.to_string path_name

let to_string_no_modules (mixed_path : t) : string =
  match mixed_path with
  | Access (path, fields) ->
    let path = PathName.to_string path in
    let fields =
      fields |> List.map (fun field -> "(" ^ PathName.to_string field ^ ")") in
    String.concat "." (path :: fields)
  | PathName path_name -> PathName.to_string_base path_name

let to_coq (mixed_path : t) : SmartPrint.t =
  !^ (to_string mixed_path)
