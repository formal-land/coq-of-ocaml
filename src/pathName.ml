(** Global identifiers with a module path, used to reference a definition for example. *)
open SmartPrint
open Monad.Notations

type t = {
  path : Name.t list;
  base : Name.t }

let tezos_imports : string list ref = ref []

let register_tezos_import (import : string) : unit =
  tezos_imports := import :: !tezos_imports

let stdlib_name = "Stdlib"

(** Internal helper for this module. *)
let __make (path : string list) (base : string) : t =
  {
    path = path |> List.map (fun name -> Name.Make name);
    base = Name.Make base
  }

(* Convert an identifier from OCaml to its Coq's equivalent, or [None] if no
   conversion is needed. We consider all the paths in the standard library
   to be converted, as conversion also means keeping the name as it (without
   taking into accounts that the stdlib was open). *)
let try_convert (path_name : t) : t option =
  let make path base = Some (__make path base) in
  let { path; base } = path_name in
  match path |> List.map Name.to_string with
  (* The core library *)
  | [] ->
    begin match Name.to_string base with
    (* Built-in types *)
    | "int" -> make [] "int"
    | "float" -> make [] "float"
    | "char" -> make [] "ascii"
    | "bytes" -> make [] "bytes"
    | "string" -> make [] "string"
    | "bool" -> make [] "bool"
    | "false" -> make [] "false"
    | "true" -> make [] "true"
    | "unit" -> make [] "unit"
    | "()" -> make [] "tt"
    | "list" -> make [] "list"
    | "[]" -> make [] "[]"
    | "op_coloncolon" -> make [] "cons"
    | "option" -> make [] "option"
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | "Ok" -> make [] "inl"
    | "Error" -> make [] "inr"
    | "exn" -> make [] "extensible_type"
    | _ -> None
    end

  (* Optional parameters *)
  | ["*predef*"] ->
    begin match Name.to_string base with
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | _ -> None
    end

  (* Specific to the Tezos protocol *)
  | ["Stdlib"; "Seq"] ->
    begin match Name.to_string base with
    | "t" -> make ["OCaml"; "Seq"] "t"
    | _ -> Some path_name
    end
  | "Tezos_raw_protocol_alpha" :: path ->
    begin match path with
    | [] -> register_tezos_import (Name.to_string base)
    | library :: _ -> register_tezos_import library
    end;
    make path (Name.to_string base)
  | "Tezos_protocol_environment_alpha__Environment" :: path
  | "Tezos_protocol_environment_alpha" :: "Environment" :: path ->
    make path (Name.to_string base)
  | head :: path ->
    begin match Util.String.is_prefix "Tezos_raw_protocol_alpha__" head with
    | None -> None
    | Some suffix ->
      register_tezos_import suffix;
      make (suffix :: path) (Name.to_string base)
    end

let convert (path_name : t) : t =
  match try_convert path_name with
  | None -> path_name
  | Some path_name -> path_name

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

(** Import an OCaml [Longident.t]. *)
let of_long_ident (is_value : bool) (long_ident : Longident.t) : t =
  (* Specific to Tezos *)
  begin match Longident.flatten long_ident with
  | ("Storage_description" as head) :: _
  | ("Storage_sigs" as head) :: _ -> register_tezos_import head
  | _ -> ()
  end;
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Unexpected Longident.t with an empty list"
  | x :: xs ->
    of_name
      (xs |> List.rev |> List.map (Name.of_string is_value))
      (Name.of_string is_value x)

(** Import an OCaml [Path.t]. *)
let of_path_without_convert (is_value : bool) (path : Path.t) : t =
  let rec aux path : (Name.t list * Name.t) =
    match path with
    | Path.Pident ident ->
      let ident_elements =
        Str.split (Str.regexp_string "__") (Ident.name ident) |>
        List.rev in
      begin match ident_elements with
      | base :: path ->
        let base =
          match path with
          | [] -> base
          | _ :: _ -> String.capitalize_ascii base in
        let path = List.map (Name.of_string is_value) path in
        let base = Name.of_string is_value base in
        (path, base)
      | [] -> assert false
      end
    | Path.Pdot (path, field) ->
      let (path, base) = aux path in
      (base :: path, Name.of_string is_value field)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  of_name (List.rev path) base

let of_path_with_convert (is_value : bool) (path : Path.t) : t =
  convert (of_path_without_convert is_value path)

let of_path_and_name_with_convert (path : Path.t) (name : Name.t) : t =
  let rec aux p : Name.t list * Name.t =
    match p with
    | Path.Pident x -> ([Name.of_ident false x], name)
    | Path.Pdot (p, s) ->
      let (path, base) = aux p in
      (Name.of_string false s :: path, base)
    | Path.Papply _ -> failwith "Unexpected path application" in
  let (path, base) = aux path in
  convert (of_name (List.rev path) base)

let map_constructor_name (cstr_name : string) (typ_ident : string) : string =
  match (cstr_name, typ_ident) with
  | ("Ed25519", "public_key_hash") -> "Ed25519Hash"
  | ("Secp256k1", "public_key_hash") -> "Secp256k1Hash"
  | ("P256", "public_key_hash") -> "P256Hash"
  | _ -> cstr_name

let of_constructor_description
  (constructor_description : Types.constructor_description)
  : t Monad.t =
  match constructor_description with
  | {
      cstr_name;
      cstr_res = { desc = Tconstr (path, _, _); _ };
      _
    } ->
    let typ_ident = Path.head path in
    let { path; _ } = of_path_without_convert false path in
    let cstr_name = map_constructor_name cstr_name (Ident.name typ_ident) in
    let base = Name.of_string false cstr_name in
    return (convert { path; base })
  | { cstr_name; _ } ->
    let path = of_name [] (Name.of_string false cstr_name) in
    raise
      path
      Unexpected
      "Unexpected constructor description without a type constructor"

let rec iterate_in_aliases (path : Path.t) : Path.t Monad.t =
  let barrier_modules = [
    "Tezos_protocol_environment_alpha__Environment";
  ] in
  let is_in_barrier_module (path : Path.t) : bool =
    List.mem (Ident.name (Path.head path)) barrier_modules in
  get_env >>= fun env ->
  match Env.find_type path env with
  | { type_manifest = Some { desc = Tconstr (path', _, _); _ }; _ } ->
    if is_in_barrier_module path && not (is_in_barrier_module path') then
      return path
    else
      iterate_in_aliases path'
  | _ -> return path

let of_label_description (label_description : Types.label_description)
  : t Monad.t =
  match label_description with
  | { lbl_name; lbl_res = { desc = Tconstr (path, _, _); _ } ; _ } ->
    iterate_in_aliases path >>= fun path ->
    let { path; base } = of_path_without_convert false path in
    let path_name = {
      path = path @ [base];
      base = Name.of_string false lbl_name } in
    return (convert path_name)
  | { lbl_name; _ } ->
    let path = of_name [] (Name.of_string false lbl_name) in
    raise
      path
      Unexpected
      "Unexpected label description without a type constructor"

let constructor_of_variant (label : string) : t Monad.t =
  let answer path base =
    return (__make path base) in
  match label with
  (* Custom variants to add here. *)
  | "Branch" -> answer ["Error_monad"] "Branch"
  | "Dir" -> answer ["Context"] "Dir"
  | "Hex" -> answer ["MBytes"] "Hex"
  | "Key" -> answer ["Context"] "Key"
  | "Permanent" -> answer ["Error_monad"] "Permanent"
  | "Temporary" -> answer ["Error_monad"] "Temporary"
  | "Uint16" -> answer ["Data_encoding"] "Uint16"
  | "Uint8" -> answer ["Data_encoding"] "Uint8"
  | _ ->
    raise
      { path = []; base = Name.of_string false label }
      NotSupported
      ("Constructor of the variant `" ^ label ^ " unknown")

let get_head_and_tail (path_name : t) : Name.t * t option =
  let { path; base } = path_name in
  match path with
  | [] -> (base, None)
  | head :: path -> (head, Some { path; base })

let add_prefix (prefix : Name.t) (path_name : t) : t =
  let { path; base } = path_name in
  { path = prefix :: path; base }

let is_tt (path_name : t) : bool =
  match (path_name.path, Name.to_string path_name.base) with
  | ([], "tt") -> true
  | _ -> false

let is_unit (path_name : t) : bool =
  match (path_name.path, Name.to_string path_name.base) with
  | ([], "unit") -> true
  | _ -> false

let false_value : t =
  { path = []; base = Name.Make "false" }

let true_value : t =
  { path = []; base = Name.Make "true" }

let prefix_by_with (path_name : t) : t =
  let { path; base } = path_name in
  { path; base = Name.prefix_by_with base }

let compare_paths (path1 : Path.t) (path2 : Path.t) : int =
  let import_path (path : Path.t) : t = of_path_without_convert false path in
  compare (import_path path1) (import_path path2)

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))

let typ_of_variant (label : string) : t option =
  let answer path base =
    Some (__make path base) in
  match label with
  (* Custom variants to add here. *)
  | "Dir" -> answer ["Context"] "dir_or_key"
  | "Key" -> answer ["Context"] "dir_or_key"
  | _ -> None

let typ_of_variants (labels : string list) : t option Monad.t =
  let typs = labels |> Util.List.filter_map typ_of_variant in
  let typs = typs |> List.sort_uniq compare in
  let variants_message =
    String.concat ", " (labels |> List.map (fun label -> "`" ^ label)) in
  match typs with
  | [] ->
    raise
      None
      NotSupported
      ("No type known for the following variants: " ^ variants_message)
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
        ))
      )
