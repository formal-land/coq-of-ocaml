(** Error messages. *)
open SmartPrint

(** An error is a location and a human message. *)
type t = {
  location : Loc.t;
  message : string }

exception Make of t

let pp (e : t) : SmartPrint.t =
  Loc.to_user e.location ^-^ !^ ":" ^^ !^ (e.message)

(** Display a warning. *)
let warn (location : Loc.t) (message : string) : unit =
  let message = "Warning: " ^ message in
  prerr_endline @@ Pp.to_string (pp {location = location; message = message})

(** Raise an exception. *)
let raise (location : Loc.t) (message : string) : 'a =
  raise (Make {location = location; message = message})

exception Json of string
