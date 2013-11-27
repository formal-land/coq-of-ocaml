(** Pretty-printing helpers. *)
open PPrint

(** Open a parenthesis according to a flag. *)
let open_paren (b : bool) : document =
  if b then lparen else empty

(** Close a parenthesis according to a flag. *)
let close_paren (b : bool) : document =
  if b then rparen else empty