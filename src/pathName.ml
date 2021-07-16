(** Global identifiers with a module path, used to reference a definition for example. *)
open SmartPrint
open Monad.Notations

type t = {
  path : Name.t list;
  base : Name.t }

(** Internal helper for this module. *)
let __make (path : string list) (base : string) : t =
  {
    path = path |> List.map (fun name -> Name.Make name);
    base = Name.Make base
  }

let to_string (x : t) : string =
  String.concat "." (List.map Name.to_string (x.path @ [x.base]))

let to_string_base (x : t) : string =
    Name.to_string x.base

let try_to_use (head : string) (name : string) : bool option Monad.t =
  let* configuration = get_configuration in
  let require = Configuration.should_require configuration head in
  let require_import = Configuration.should_require_import configuration head in
  match (require, require_import) with
  | (_, Some require_import) ->
    let* () = use true require_import name in
    return (Some true)
  | (Some require, _) ->
    let* () = use false require name in
    return (Some false)
  | (None, None) -> return None

(* Convert an identifier from OCaml to its Coq's equivalent, or [None] if no
   conversion is needed. We consider all the paths in the standard library
   to be converted, as conversion also means keeping the name as it (without
   taking into accounts that the stdlib was open). *)
let try_convert (path_name : t) : t option Monad.t =
  let make path base =
    return (Some (__make path base)) in
  let { path; base } = path_name in
  let path = path |> List.map Name.to_string in
  let base = Name.to_string base in
  let* renamed_path_name =
    match (path, base) with
    | (source :: name :: rest, _) ->
      let* is_import = try_to_use source name in
      begin match is_import with
      | None -> return None
      | Some import ->
        if import then
          make rest base
        else
          make (name :: rest) base
      end
    | ([source], name) ->
      let* is_import = try_to_use source name in
      begin match is_import with
      | None -> return None
      | Some _ -> make [] base
      end
    | _ -> return None in
  let* configuration = get_configuration in
  let path_name_rewrite =
    Configuration.is_in_renaming_rule configuration
      (to_string (Option.value renamed_path_name ~default:path_name)) in
  match path_name_rewrite with
  | Some path_name ->
    begin match List.rev (String.split_on_char '.' path_name) with
    | [] -> failwith "Unexpected empty list"
    | base :: rev_path -> make (List.rev rev_path) base
    end
  | None ->
    begin match path_name.path with
    | Name.Make "Stdlib" :: _ -> return (Some path_name)
    | _ -> return renamed_path_name
    end

let convert (path_name : t) : t Monad.t =
  try_convert path_name >>= fun conversion ->
  match conversion with
  | None -> return path_name
  | Some path_name -> return path_name

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

(* Import an OCaml [Longident.t]. *)
let of_long_ident (is_value : bool) (long_ident : Longident.t) : t Monad.t =
  let* configuration = get_configuration in
  let* () =
    match Longident.flatten long_ident with
    | head :: _ ->
      let require =
        Configuration.should_require_long_ident configuration head in
      begin match require with
      | None -> return ()
      | Some require -> use false require head
      end
    | [] -> return () in
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Unexpected Longident.t with an empty list"
  | x :: xs ->
    (xs |> List.rev |> Monad.List.map (Name.of_string is_value)) >>= fun path ->
    let* name = Name.of_string is_value x in
    return (of_name path name)

(** Split an [Ident.t] in case of flattened module names. *)
let split_ident (is_value : bool) (ident : Ident.t)
  : (Name.t list * Name.t) Monad.t =
  let ident_elements =
    Str.split (Str.regexp_string "__") (Ident.name ident) |>
    List.rev in
  match ident_elements with
  | base :: path ->
    let base =
      match path with
      | [] -> base
      | _ :: _ -> String.capitalize_ascii base in
    let* path = Monad.List.map (Name.of_string false) path in
    let* base = Name.of_string is_value base in
    return (List.rev path, base)
  | [] -> assert false

(** Import an OCaml [Path.t]. *)
let of_path_without_convert (is_value : bool) (path : Path.t) : t Monad.t =
  let rec aux path : (Name.t list * Name.t) Monad.t =
    match path with
    | Path.Pident ident -> split_ident is_value ident
    | Path.Pdot (path, field) ->
      aux path >>= fun (path, base) ->
      Name.of_string is_value field >>= fun field ->
      return (base :: path, field)
    | Path.Papply _ -> failwith "Unexpected functor path application" in
  aux path >>= fun (path, base) ->
  return (of_name (List.rev path) base)

let of_path_with_convert (is_value : bool) (path : Path.t) : t Monad.t =
  of_path_without_convert is_value path >>= fun path ->
  convert path

let of_path_and_name_with_convert (path : Path.t) (name : Name.t) : t Monad.t =
  let rec aux p : (Name.t list * Name.t) Monad.t =
    match p with
    | Path.Pident x ->
      let* (path, base) = split_ident false x in
      return (path @ [base], name)
    | Path.Pdot (p, s) ->
      aux p >>= fun (path, base) ->
      Name.of_string false s >>= fun s ->
      return (path @ [s], base)
    | Path.Papply _ -> failwith "Unexpected functor path application" in
  aux path >>= fun (path, base) ->
  convert (of_name path base)

let map_constructor_name (cstr_name : string) (typ_ident : string)
  : string Monad.t =
  let* configuration = get_configuration in
  let renaming =
    Configuration.is_constructor_renamed configuration typ_ident cstr_name in
  match renaming with
  | Some renaming -> return renaming
  | None -> return cstr_name

let rec iterate_in_aliases (path : Path.t) (nb_args : int) : Path.t Monad.t =
  let* configuration = get_configuration in
  let is_in_barrier_module (path : Path.t) : bool =
    match Path.head path with
    | head ->
      Configuration.is_alias_in_barrier_module configuration (Ident.name head)
    | exception _ -> false in
  let* env = get_env in
  match Env.find_type path env with
  | { type_manifest = Some { desc = Tconstr (path', args, _); _ }; _ }
    when List.length args = nb_args ->
    if is_in_barrier_module path && not (is_in_barrier_module path') then
      return path
    else
      iterate_in_aliases path' nb_args
  | _ -> return path

let of_constructor_description
  (constructor_description : Types.constructor_description)
  : t Monad.t =
  match constructor_description with
  | {
      cstr_name;
      cstr_res = { desc = Tconstr (path, args, _); _ };
      _
    } ->
    let* path = iterate_in_aliases path (List.length args) in
    let typ_ident = Path.head path in
    of_path_without_convert false path >>= fun { path; _ } ->
    let* cstr_name = map_constructor_name cstr_name (Ident.name typ_ident) in
    Name.of_string false cstr_name >>= fun base ->
    convert { path; base }
  | { cstr_name; _ } ->
    Name.of_string false cstr_name >>= fun cstr_name ->
    let path = of_name [] cstr_name in
    raise
      path
      Unexpected
      "Unexpected constructor description without a type constructor"

let of_label_description (label_description : Types.label_description)
  : t Monad.t =
  match label_description with
  | { lbl_name; lbl_res = { desc = Tconstr (path, args, _); _ } ; _ } ->
    let* path = iterate_in_aliases path (List.length args) in
    of_path_without_convert false path >>= fun { path; base } ->
    Name.of_string false lbl_name >>= fun lbl_name ->
    let path_name = {
      path = path @ [base];
      base = lbl_name } in
    convert path_name
  | { lbl_name; _ } ->
    Name.of_string false lbl_name >>= fun lbl_name ->
    let path = of_name [] lbl_name in
    raise
      path
      Unexpected
      "Unexpected label description without a type constructor"

let constructor_of_variant (label : string) : t Monad.t =
  let* configuration = get_configuration in
  let constructor =
    Configuration.get_variant_constructor configuration label in
  match constructor with
  | Some constructor ->
    return { path = []; base = Name.of_string_raw constructor }
  | None ->
    Name.of_string false label >>= fun base ->
    raise
      { path = []; base }
      NotSupported
      ("Constructor of the variant `" ^ label ^ " unknown")

let add_prefix (prefix : Name.t) (path_name : t) : t =
  let { path; base } = path_name in
  { path = prefix :: path; base }

let is_tt (path_name : t) : bool =
  match (path_name.path, Name.to_string path_name.base) with
  | ([], "tt") -> true
  | _ -> false

let is_unit (path : Path.t) : bool =
  Path.name path = "unit"

let false_value : t =
  { path = []; base = Name.Make "false" }

let true_value : t =
  { path = []; base = Name.Make "true" }

let unit_value : t =
  { path = []; base = Name.Make "tt" }

let prefix_by_with (path_name : t) : t =
  let { path; base } = path_name in
  { path; base = Name.prefix_by_with base }

let compare_paths (path1 : Path.t) (path2 : Path.t) : int Monad.t =
  let import_path (path : Path.t) : t Monad.t =
    of_path_without_convert false path in
  import_path path1 >>= fun path1 ->
  import_path path2 >>= fun path2 ->
  return (compare path1 path2)

let to_coq (x : t) : SmartPrint.t =
  !^ (to_string x)

let to_name (is_value : bool) (x : t) : Name.t Monad.t =
  let s =
    to_string x |> String.map (fun c ->
      if c = '.' then
        '_'
      else
        c
    ) in
  Name.of_string is_value s

let typ_of_variant (label : string) : t option Monad.t =
  let* configuration = get_configuration in
  let typ = Configuration.get_variant_typ configuration label in
  match typ with
  | Some typ -> return (Some { path = []; base = Name.of_string_raw typ })
  | None -> return None

let typ_of_variants (labels : string list) : t option Monad.t =
  let* typs = labels |> Monad.List.filter_map typ_of_variant in
  let typs = typs |> List.sort_uniq compare in
  let variants_message =
    String.concat ", " (labels |> List.map (fun label -> "`" ^ label)) in
  let variant_help_error_message =
    "Try using non-variant algebraic data types, or configure the " ^
    "variants in the configuration file." in
  match typs with
  | [] ->
    raise
      None
      NotSupported
      (
        "No type known for the following variants: " ^ variants_message ^
        "\n\n" ^
        variant_help_error_message
      )
  | [typ] -> return (Some typ)
  | typ :: _ :: _ ->
    raise
      (Some typ)
      NotSupported
      (
        "At least two types found for the variants " ^ variants_message ^
        ":\n" ^
        String.concat "\n" (typs |> List.map (fun typ ->
          "- " ^ Pp.to_string (to_coq typ)
        )) ^
        "\n\n" ^
        variant_help_error_message
      )

let is_variant_declaration
    (path : Path.t)
  : (Types.constructor_declaration list * Types.type_expr list) option Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_variant constructors; type_params = params; _ } -> return @@ Some (constructors, params)
  | _ | exception _ -> return None

let is_record
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_record _; _ } -> return true
  | _ | exception _ -> return false

let is_tagged_variant
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_variant _; type_attributes; _ } ->
    let* type_attributes = Attribute.of_attributes type_attributes in
    return @@ Attribute.has_tag_gadt type_attributes
  | { type_kind = Type_record _; _ } -> return true
  | _ | exception _ -> return false


let is_native_type (path : Path.t) : bool =
   let name = Path.last path in
   List.exists (function x -> name = x) ["int"; "bool"; "string"; "unit"]

let is_native_datatype (path : Path.t) : bool =
   let name = Path.last path in
   List.exists (function x -> name = x) ["list"; "option"; "map"]


let prim_proj_fst : t =
  {base = Name.of_string_raw "fst";
   path = [Name.of_string_raw "Primitive"]
  }

let prim_proj_snd : t =
  { base = Name.of_string_raw "snd";
    path = [Name.of_string_raw "Primitive"]
  }
