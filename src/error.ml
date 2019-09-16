(** Error messages. *)

module Category = struct
  type t =
    | FirstClassModule
    | NotFound
    | NotSupported
    | SideEffect
    | Unexpected

  let to_string (category : t) : string =
    match category with
    | FirstClassModule -> "First class module"
    | NotFound -> "Not found"
    | NotSupported -> "Not supported"
    | SideEffect -> "Side effect"
    | Unexpected -> "Unexpected"
end

(** Display a warning. *)
let warn (loc : Loc.t) (message : string) : unit =
  let message = "Warning: " ^ message in
  prerr_endline (Loc.to_string loc ^ ": " ^ message)

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

let get_code_frame (source_lines : string list) (line_number : int) : string =
  let output_lines : string list ref = ref [] in
  let nb_source_lines = List.length source_lines in
  let first_line_number = line_number - 2 in
  let last_line_number = line_number + 3 in
  let line_number_width = String.length (string_of_int last_line_number) in
  for current_line_number = first_line_number to last_line_number do
    let current_line_index = current_line_number - 1 in
    begin if current_line_index >= 0 && current_line_index < nb_source_lines then
      let is_error_line = current_line_number = line_number in
      let current_line =
          (if is_error_line then colorize "31;1" "> " else "  ") ^
          colorize (if is_error_line then "1" else "0") (
            pad line_number_width ' ' "" (string_of_int current_line_number) ^ " | "
          ) ^
          colorize (if is_error_line then "33;1" else "33") (List.nth source_lines current_line_index) in
      output_lines := colorize (if is_error_line then "1" else "") current_line :: !output_lines
    end
  done;
  String.concat "\n" (List.rev !output_lines)

let display_error
  (source_lines : string list)
  (loc : Loc.t)
  (category : Category.t)
  (message : string)
  : unit =
  print_endline (
    colorize "34;1" (
      pad 100 '-'
        ("--- " ^ loc.file_name ^ ":" ^ string_of_int loc.start.line ^ " ")
        (" " ^ Category.to_string category ^ " ---")
    ) ^ "\n" ^
    "\n" ^
    get_code_frame source_lines loc.start.line ^ "\n" ^
    "\n\n" ^
    message ^
    "\n\n"
  )

let read_source_file (source_file : string) : string =
  let channel = open_in source_file in
  let length = in_channel_length channel in
  really_input_string channel length

let display_errors
  (source_file : string)
  (errors : (Loc.t * Category.t * string) list)
  : unit =
  let source_file_content = read_source_file source_file in
  let source_lines = String.split_on_char '\n' source_file_content in
  errors |> List.iteri (fun index (loc, category, message) ->
    display_error source_lines loc category message
  );
  let nb_errors = List.length errors in
  print_endline (
    colorize "34;1" (
      pad (100 + 20) '-'
        "--- Failure "
        ("[ " ^
          colorize "31" (string_of_int nb_errors ^ (if nb_errors = 1 then " error" else " errors")) ^
          colorize "34;1" " ]---")
      ) ^ "\n" ^
    "\n\n" ^
    colorize "" ("Cannot import '" ^ source_file ^ "' to Coq.") ^ "\n" ^
    "\n"
  )
