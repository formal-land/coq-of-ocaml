(** Extraction of effects *)

exception Fail of string

let div n =
  if n = 0 then
    raise (Fail "n is null")
  else
    256 / n