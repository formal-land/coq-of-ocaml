(** Pretty-printing helpers. *)
open SmartPrint

let list (ds : SmartPrint.t list) : SmartPrint.t =
  parens (nest (separate (!^ "," ^^ space) ds))

let parens (b : bool) (d : SmartPrint.t) : SmartPrint.t =
  if b then
    parens d
  else
    d