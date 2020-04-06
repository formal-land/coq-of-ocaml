type t = {
  file_name : string;
  without_guard_checking : string list;
  without_positivity_checking : string list;
}

let default (file_name : string) : t = {
  file_name;
  without_guard_checking = [];
  without_positivity_checking = [];
}

let is_without_guard_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_guard_checking

let is_without_positivity_checking (configuration : t) : bool =
  List.mem configuration.file_name configuration.without_positivity_checking

let get_string_list (json : Yojson.Basic.t) : string list =
  let error_message = "Expected a string list" in
  match json with
  | `List jsons ->
    jsons |> List.map (function
      | `String value -> value
      | _ -> failwith error_message
    )
  | _ -> failwith error_message

let of_json (file_name : string) (json : Yojson.Basic.t) : t =
  match json with
  | `Assoc entries ->
    List.fold_left
      (fun configuration (id, entry) ->
        match id with
        | "without_guard_checking" ->
          {configuration with without_guard_checking = get_string_list entry}
        | "without_positivity_checking" ->
          {configuration with
            without_positivity_checking = get_string_list entry}
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
