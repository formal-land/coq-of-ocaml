open SmartPrint

type t = {
  location : Loc.t;
  message : string }

exception Make of t

let pp (e : t) : SmartPrint.t =
  Loc.pp e.location ^-^ !^ ":" ^^ !^ (e.message)

let raise (location : Loc.t) (message : string) : 'a =
  raise (Make {location = location; message = message})