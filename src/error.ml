(** Error messages. *)
open SmartPrint

module Category = struct
  type t =
    | ExtensibleType
    | Merlin
    | Module
    | NotSupported
    | SideEffect
    | Unexpected

  let to_id (category : t) : string =
    match category with
    | ExtensibleType -> "extensible_type"
    | Merlin -> "merlin"
    | Module -> "module"
    | NotSupported -> "not_supported"
    | SideEffect -> "side_effect"
    | Unexpected -> "unexpected"
end

type t = {
  category : Category.t;
  loc : Loc.t;
  message : string;
}

let to_comment (error_message : string) : SmartPrint.t =
  !^ ("(* ❌ " ^ List.hd (String.split_on_char '\n' error_message) ^ " *)")

let pad
  (width : int)
  (character : char)
  (message_left : string)
  (message_right : string)
  : string =
  let total_length = String.length message_left + String.length message_right in
  let padding_text = String.make (max 0 (width - total_length)) character in
  message_left ^ padding_text ^ message_right

let colorize (color : string) (message : string) : string =
  "\027[" ^ color ^ "m" ^ message ^ "\027[0m"

let colorize_line (content : string) (loc : Loc.t) (line_number : int) : string =
  let left_limit =
    if line_number < loc.start.line then
      String.length content
    else if line_number = loc.start.line then
      loc.start.character - 1
    else
      0 in
  let right_limit =
    if line_number < loc.end_.line then
      String.length content
    else if line_number = loc.end_.line then
      loc.end_.character - 1
    else
      0 in
  colorize "33" (String.sub content 0 (left_limit - 0)) ^
  colorize "33;1" (String.sub content left_limit (right_limit - left_limit)) ^
  colorize "33" (String.sub content right_limit (String.length content - right_limit))


let get_code_frame (source_lines : string list) (loc : Loc.t) : string =
  let output_lines : string list ref = ref [] in
  let nb_source_lines = List.length source_lines in
  let nb_lines_above = 2 in
  let nb_lines_below = 3 in
  let first_line_number = loc.start.line - nb_lines_above in
  let last_line_number = loc.end_.line + nb_lines_below in
  let line_number_width = String.length (string_of_int last_line_number) in
  for current_line_number = first_line_number to last_line_number do
    let current_line_index = current_line_number - 1 in
    begin if current_line_index >= 0 && current_line_index < nb_source_lines then
      let current_line_content = List.nth source_lines current_line_index in
      let is_error_line =
        loc.start.line <= current_line_number &&
        current_line_number <= loc.end_.line in
      let line_head = if is_error_line then colorize "31;1" "> " else "  " in
      let line_number =
        colorize (if is_error_line then "1" else "0") (
          pad line_number_width ' ' "" (string_of_int current_line_number) ^ " | "
        ) in
      let line_content =
        colorize_line current_line_content loc current_line_number in
      let current_line = line_head ^ line_number ^ line_content in
      output_lines := colorize (if is_error_line then "1" else "") current_line :: !output_lines
    end
  done;
  String.concat "\n" (List.rev !output_lines)

let display_error
  (file_name : string)
  (source_lines : string list)
  (loc : Loc.t)
  (category : Category.t)
  (message : string)
  (error_number : int)
  (number_of_errors : int)
  : string =
  colorize "34;1" (
    pad 100 '-'
      ("--- " ^ file_name ^
        ":" ^ string_of_int loc.start.line ^
        ":" ^ string_of_int loc.start.character ^
        " "
      )
      (" " ^ Category.to_id category ^
        " (" ^ string_of_int error_number ^ "/" ^ string_of_int number_of_errors ^ ")" ^
        " ---"
      )
  ) ^ "\n" ^
  "\n" ^
  get_code_frame source_lines loc ^ "\n" ^
  "\n\n" ^
  message ^
  "\n\n"

let display_errors_human
  (source_file_name : string)
  (source_file_content : string)
  (errors : t list)
  : string =
  let source_lines = String.split_on_char '\n' source_file_content in
  let error_messages =
    errors |>
    List.mapi (fun index { category; loc; message } ->
      display_error source_file_name source_lines loc category message
        (index + 1) (List.length errors)
    ) |>
    String.concat "" in
  let nb_errors = List.length errors in
  error_messages ^
  colorize "34;1" (
    pad (100 + 20) '-'
      "--- Errors "
      ("[ " ^
        colorize "31" (string_of_int nb_errors ^ (if nb_errors = 1 then " error" else " errors")) ^
        colorize "34;1" " ]---")
    ) ^ "\n"

let display_errors_json (errors : t list) : string =
  Yojson.pretty_to_string ~std:true (
    `List (errors |> List.map (fun { category; loc; message } ->
      `Assoc [
        ("category", `String (Category.to_id category));
        ("location", `Assoc [
          ("end", `Int loc.end_.character);
          ("start", `Int loc.start.character);
        ]);
        ("message", `String message);
      ]
    ))
  ) ^ "\n"

let display_errors
  (json_mode : bool)
  (source_file_name : string)
  (source_file_content : string)
  (errors : t list)
  : string =
  let errors =
    errors |>
    List.sort (fun error1 error2 ->
      compare error1.loc.start.line error2.loc.start.line
    ) in
  if not json_mode then
    display_errors_human source_file_name source_file_content errors
  else
    display_errors_json errors
