module ConstructorMapping = struct
  type t = {
    source : string;
    target : string;
    typ : string;
  }
end

module Import = struct
  type t = {
    source : string;
    target : string;
  }
end

module MonadicOperator = struct
  type t = {
    name : string;
    notation : string;
  }
end

module VariantMapping = struct
  type t = {
    source : string;
    target : string;
  }
end

type t = {
  alias_barrier_modules : string list;
  constructor_map : ConstructorMapping.t list;
  error_blacklist : string list;
  error_filename_blacklist : string list;
  escape_value : string list;
  file_name : string;
  first_class_module_path_blacklist : string list;
  head_suffix : string;
  monadic_operators : MonadicOperator.t list;
  require : Import.t list;
  require_import : Import.t list;
  require_long_ident : Import.t list;
  require_mli : string list;
  variant_constructors : VariantMapping.t list;
  variant_types : VariantMapping.t list;
  without_guard_checking : string list;
  without_positivity_checking : string list;
}

let default (file_name : string) : t = {
  alias_barrier_modules = [];
  constructor_map = [];
  error_blacklist = [];
  error_filename_blacklist = [];
  escape_value = [];
  file_name;
  first_class_module_path_blacklist = [];
  head_suffix = "";
  monadic_operators = [];
  require = [];
  require_import = [];
  require_long_ident = [];
  require_mli = [];
  variant_constructors = [];
  variant_types = [];
  without_guard_checking = [];
  without_positivity_checking = [];
}

let is_alias_in_barrier_module (configuration : t) (name : string) : bool =
  List.mem name configuration.alias_barrier_modules

let is_constructor_renamed (configuration : t) (typ : string) (name : string)
  : string option =
  configuration.constructor_map |>
  List.find_opt (fun { ConstructorMapping.source; typ = typ'; _ } ->
    source = name && typ' = typ
  ) |>
  Option.map (fun { ConstructorMapping.target; _ } -> target)

let is_error_in_blacklist (configuration : t) (error_id : string) : bool =
  List.mem error_id configuration.error_blacklist

let is_filename_in_error_blacklist (configuration : t) : bool =
  List.mem configuration.file_name configuration.error_filename_blacklist

let is_value_to_escape (configuration : t) (name : string) : bool =
  List.mem name configuration.escape_value

let is_in_first_class_module_backlist (configuration : t) (path : Path.t)
  : bool =
  match Path.to_string_list path with
  | head :: _ :: []
    when List.mem head configuration.first_class_module_path_blacklist ->
    true
  | _ -> false

let is_monadic_operator (configuration : t) (name : string) : string option =
  let monadic_operator =
    List.find_opt
      (fun { MonadicOperator.name = name'; _ } -> name' = name)
      configuration.monadic_operators in
  match monadic_operator with
  | None -> None
  | Some { MonadicOperator.notation; _ } -> Some notation

let should_require (configuration : t) (base : string)
  : string option =
  configuration.require |>
  List.find_opt (fun { Import.source; _ } -> source = base) |>
  Option.map (fun { Import.target; _ } -> target)

let should_require_import (configuration : t) (base : string)
  : string option =
  configuration.require_import |>
  List.find_opt (fun { Import.source; _ } -> source = base) |>
  Option.map (fun { Import.target; _ } -> target)

let should_require_long_ident (configuration : t) (base : string)
  : string option =
  configuration.require_long_ident |>
  List.find_opt (fun { Import.source; _ } -> source = base) |>
  Option.map (fun { Import.target; _ } -> target)

let is_require_mli (configuration : t) (name : string) : bool =
  List.mem name configuration.require_mli

let get_variant_constructor (configuration : t) (name : string) : string option =
  configuration.variant_constructors |>
  List.find_opt (fun { VariantMapping.source; _ } ->
    source = name
  ) |>
  Option.map (fun { VariantMapping.target; _ } -> target)

let get_variant_typ (configuration : t) (name : string) : string option =
  configuration.variant_types |>
  List.find_opt (fun { VariantMapping.source; _ } ->
    source = name
  ) |>
  Option.map (fun { VariantMapping.target; _ } -> target)

let is_without_guard_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_guard_checking

let is_without_positivity_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_positivity_checking

let get_string (id : string) (json : Yojson.Basic.t) : string =
  let error_message = "Expected a string list in " ^ id in
  match json with
  | `String value -> value
  | _ -> failwith error_message

let get_string_list (id : string) (json : Yojson.Basic.t) : string list =
  let error_message = "Expected a string list in " ^ id in
  match json with
  | `List jsons ->
    jsons |> List.map (function
      | `String value -> value
      | _ -> failwith error_message
    )
  | _ -> failwith error_message

let get_string_couple_list (id : string) (json : Yojson.Basic.t)
  : (string * string) list =
  let error_message = "Expected a list of couples of strings in " ^ id in
  match json with
  | `List jsons ->
    jsons |> List.map (function
      | `List [`String value1; `String value2] -> (value1, value2)
      | _ -> failwith error_message
    )
  | _ -> failwith error_message

let get_string_triple_list (id : string) (json : Yojson.Basic.t)
  : (string * string * string) list =
  let error_message = "Expected a list of triples of strings in " ^ id in
  match json with
  | `List jsons ->
    jsons |> List.map (function
      | `List [`String value1; `String value2; `String value3] ->
        (value1, value2, value3)
      | _ -> failwith error_message
    )
  | _ -> failwith error_message

let of_json (file_name : string) (json : Yojson.Basic.t) : t =
  match json with
  | `Assoc entries ->
    List.fold_left
      (fun configuration (id, entry) ->
        match id with
        | "alias_barrier_modules" ->
          let entry = get_string_list "alias_barrier_modules" entry in
          {configuration with alias_barrier_modules = entry}
        | "constructor_map" ->
          let entry =
            entry |>
            get_string_triple_list "constructor_map" |>
            List.map (fun (typ, source, target) ->
              { ConstructorMapping.source; target; typ }
            ) in
          {configuration with constructor_map = entry}
        | "error_blacklist" ->
          let entry = get_string_list "error_blacklist" entry in
          {configuration with error_blacklist = entry}
        | "error_filename_blacklist" ->
          let entry = get_string_list "error_filename_blacklist" entry in
          {configuration with error_filename_blacklist = entry}
        | "escape_value" ->
          let entry = get_string_list "escape_value" entry in
          {configuration with escape_value = entry}
        | "first_class_module_path_blacklist" ->
          let entry = get_string_list "first_class_module_path_blacklist" entry in
          {configuration with first_class_module_path_blacklist = entry}
        | "head_suffix" ->
          let entry = get_string "head_suffix" entry in
          {configuration with head_suffix = entry}
        | "monadic_operators" ->
          let entry =
            entry |>
            get_string_couple_list "monadic_operators" |>
            List.map (fun (name, notation) ->
              { MonadicOperator.name; notation }
            ) in
          {configuration with monadic_operators = entry}
        | "require" ->
          let entry =
            entry |>
            get_string_couple_list "require" |>
            List.map (fun (source, target) -> { Import.source; target }) in
          {configuration with require = entry}
        | "require_import" ->
          let entry =
            entry |>
            get_string_couple_list "require_import" |>
            List.map (fun (source, target) -> { Import.source; target }) in
          {configuration with require_import = entry}
        | "require_long_ident" ->
          let entry =
            entry |>
            get_string_couple_list "require_long_ident" |>
            List.map (fun (source, target) -> { Import.source; target }) in
          {configuration with require_long_ident = entry}
        | "require_mli" ->
          let entry = get_string_list "require_mli" entry in
          {configuration with require_mli = entry}
        | "variant_constructors" ->
          let entry =
            entry |>
            get_string_couple_list "variant_constructors" |>
            List.map (fun (source, target) ->
              { VariantMapping.source; target }
            ) in
          {configuration with variant_constructors = entry}
        | "variant_types" ->
          let entry =
            entry |>
            get_string_couple_list "variant_types" |>
            List.map (fun (source, target) ->
              { VariantMapping.source; target }
            ) in
          {configuration with variant_types = entry}
        | "without_guard_checking" ->
          let entry = get_string_list "without_guard_checking" entry in
          {configuration with without_guard_checking = entry}
        | "without_positivity_checking" ->
          let entry = get_string_list "without_positivity_checking" entry in
          {configuration with without_positivity_checking = entry}
        | _ -> failwith ("Unknown entry " ^ id)
      )
      (default file_name)
      entries
  | _ -> failwith "Expected an object {...}"

let of_optional_file_name
  (source_file_name : string) (configuration_file_name : string option) : t =
  match configuration_file_name with
  | None -> default source_file_name
  | Some configuration_file_name ->
    let json =
      Yojson.Basic.from_file
        ~fname:configuration_file_name
        configuration_file_name in
    of_json source_file_name json
