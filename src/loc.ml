open Sexplib.Std
open SmartPrint

module Position = struct
  type t = {
    file_name : string;
    line : int }
    [@@deriving sexp]

  let of_position (position : Lexing.position) : t =
    { file_name = position.Lexing.pos_fname ; line = position.Lexing.pos_lnum }
end

type t =
  | Unknown
  | Known of Position.t * Position.t
  [@@deriving sexp]

let pp (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Known (start, _) ->
    OCaml.int start.line

let to_user (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Known ({ file_name; line }, _) ->
    !^ file_name ^-^ !^ "," ^^ !^ "line" ^^ OCaml.int line

let of_location (l : Location.t) : t =
  Known (Position.of_position l.Location.loc_start, Position.of_position l.Location.loc_end)
