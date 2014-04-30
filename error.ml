open SmartPrint

type t = {
  location : Loc.t;
  message : string }

exception Make of t

let pp (e : t) : SmartPrint.t =
  Loc.pp e.location ^-^ !^ ":" ^^ !^ (e.message)

let warn (location : Loc.t) (message : string) : unit =
  prerr_endline @@ to_string 80 2 (pp {location = location; message = message})

let raise (location : Loc.t) (message : string) : 'a =
  raise (Make {location = location; message = message})

exception Json of string