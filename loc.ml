open SmartPrint

type t =
  | Unknown
  | Ether of PathName.t (** For pre-defined values. *)
  | Concrete of Lexing.position * Lexing.position

let pp (l : t) : SmartPrint.t =
  match l with
  | Unknown -> !^ "?"
  | Ether x -> !^ "Ether" ^^ PathName.pp x
  | Concrete (start, _) ->
    let (_, line, _) = Location.get_pos_info start in
    OCaml.int line

let of_location (l : Location.t) : t =
  Concrete (l.Location.loc_start, l.Location.loc_end)