(** Error messages. *)
open SmartPrint

(** Display a warning. *)
let warn (loc : Loc.t) (message : string) : unit =
  let message = "Warning: " ^ message in
  prerr_endline (Loc.to_string loc ^ ": " ^ message)

let left_pad (message : string) (width : int) : string =
  String.make (max 0 (width - String.length message)) ' ' ^ message

let get_code_frame (source_lines : string list) (line_number : int) : string =
  let output_lines : string list ref = ref [] in
  let nb_source_lines = List.length source_lines in
  let first_line_number = line_number - 2 in
  let last_line_number = line_number + 3 in
  let line_number_width = String.length (string_of_int last_line_number) in
  for current_line_number = first_line_number to last_line_number do
    let current_line_index = current_line_number - 1 in
    begin if current_line_index >= 0 && current_line_index < nb_source_lines then
      let current_line =
          (if current_line_number = line_number then "> " else "  ") ^
          left_pad (string_of_int current_line_number) line_number_width ^ " | " ^
          List.nth source_lines current_line_index in
      output_lines := current_line :: !output_lines
    end
  done;
  String.concat "\n" (List.rev !output_lines)

let display_error (source_lines : string list) (loc : Loc.t) (message : string) : unit =
  print_endline (
    Loc.to_string loc ^ ":" ^ "\n" ^
    get_code_frame source_lines loc.start.line ^ "\n" ^
    "\n" ^
    message
  )

let display_separator () : unit =
  print_endline ("\n" ^ String.make 80 '-' ^ "\n")
