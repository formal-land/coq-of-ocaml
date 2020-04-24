module Import = struct
  type t = {
    source : string;
    target : string;
  }
end

type t = {
  file_name : string;
  require : Import.t list;
  require_import : Import.t list;
  without_guard_checking : string list;
  without_positivity_checking : string list;
}

let default (file_name : string) : t = {
  file_name;
  require = [];
  require_import = [];
  without_guard_checking = [];
  without_positivity_checking = [];
}

let should_require (configuration : t) (base : string)
  : (string * bool) option =
  let require =
    configuration.require |> List.find_opt (fun { Import.source; _ } ->
      source = base
    ) in
  let require_import =
    configuration.require_import |> List.find_opt (fun { Import.source; _ } ->
      source = base
    ) in
  match (require, require_import) with
  | (Some { Import.target; _ }, _) -> Some (target, false)
  | (_, Some { Import.target; _ }) -> Some (target, true)
  | (None, None) -> None

let is_without_guard_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_guard_checking

let is_without_positivity_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_positivity_checking

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

let of_json (file_name : string) (json : Yojson.Basic.t) : t =
  match json with
  | `Assoc entries ->
    List.fold_left
      (fun configuration (id, entry) ->
        match id with
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
