module Position = struct
  type t = {
    line : int;
  }

  let of_position (position : Lexing.position) : t =
    { line = position.Lexing.pos_lnum }
end

type t = {
  end_ : Position.t;
  file_name : string;
  start : Position.t;
  }

let to_string (loc : t) : string =
  loc.file_name ^ "," ^ " line " ^ string_of_int loc.start.Position.line

let of_location (location : Location.t) : t =
  let start = location.Location.loc_start in
  let end_ = location.Location.loc_end in
  {
    end_ = Position.of_position end_;
    file_name = start.Lexing.pos_fname;
    start = Position.of_position start;
  }
