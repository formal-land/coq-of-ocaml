open SmartPrint

type t =
  | Unknown
  | Concrete of Lexing.position * Lexing.position
  | Ether of Name.t

let pp (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Concrete (start, _) ->
    let (_, line, _) = Location.get_pos_info start in
    OCaml.int line
  | Ether x -> !^ "Ether" ^-^ parens (Name.pp x)

let of_location (l : Location.t) : t =
  Concrete (l.Location.loc_start, l.Location.loc_end)