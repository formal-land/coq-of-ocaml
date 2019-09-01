(** Error messages. *)
open SmartPrint

(** An error is a location and a human message. *)
type t = {
  location : Loc.t;
  message : string }

let pp (e : t) : SmartPrint.t =
  Loc.to_user e.location ^-^ !^ ":" ^^ !^ (e.message)

(** Display a warning. *)
let warn (location : Loc.t) (message : string) : unit =
  let message = "Warning: " ^ message in
  prerr_endline @@ Pp.to_string (pp {location = location; message = message})
