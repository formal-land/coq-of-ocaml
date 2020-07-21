open SmartPrint
open Monad.Notations

type t =
  | Set
  | Tag of Name.t

let to_string (k : t) : string =
  match k with
  | Set -> "Set"
  | Tag name -> Name.to_string name
