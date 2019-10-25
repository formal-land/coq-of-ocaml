module Position = struct
  type t = {
    line : int;
  }

  let of_position (position : Lexing.position) : t =
    { line = position.Lexing.pos_lnum }
end

type t = {
  end_ : Position.t;
  start : Position.t;
  }

let to_string (file_name : string) (loc : t) : string =
  file_name ^ "," ^ " line " ^ string_of_int loc.start.Position.line

let of_location (location : Location.t) : t =
  let end_ = location.Location.loc_end in
  let start = location.Location.loc_start in
  {
    end_ = Position.of_position end_;
    start = Position.of_position start;
  }
