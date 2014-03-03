open SmartPrint

type t = (Lexing.position * Lexing.position) option

let unknown : t = None

let pp (l : t) : SmartPrint.t =
  match l with
  | None -> !^ "?"
  | Some (start, _) ->
    let (_, line, _) = Location.get_pos_info start in
    OCaml.int line

let of_location (l : Location.t) : t =
  Some (l.Location.loc_start, l.Location.loc_end)