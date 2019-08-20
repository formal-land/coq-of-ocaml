open Sexplib.Std
open SmartPrint

module Position = struct
  type t = {
    line : int }
    [@@deriving sexp]

  let of_position (position : Lexing.position) : t =
    { line = position.Lexing.pos_lnum }
end

type t =
  | Unknown
  | Known of string * Position.t * Position.t
  [@@deriving sexp]

let to_user (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Known (file_name, { line }, _) ->
    !^ file_name ^-^ !^ "," ^^ !^ "line" ^^ OCaml.int line

let of_location (l : Location.t) : t =
  let start = l.Location.loc_start in
  let _end = l.Location.loc_end in
  Known (start.Lexing.pos_fname, Position.of_position start, Position.of_position _end)
