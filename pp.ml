(** Pretty-printing helpers. *)
open SmartPrint

(*(** Open a parenthesis according to a flag. *)
let open_paren (b : bool) : SmartPrint.t =
  if b then !^ "(" else empty

(** Close a parenthesis according to a flag. *)
let close_paren (b : bool) : SmartPrint.t =
  if b then !^ ")" else empty*)

let parens (b : bool) (d : SmartPrint.t) : SmartPrint.t =
  if b then
    parens d
  else
    d