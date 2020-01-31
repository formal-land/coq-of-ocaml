open SmartPrint

let parens (b : bool) (doc : SmartPrint.t) : SmartPrint.t =
  if b then
    parens doc
  else
    doc

let primitive_tuple (docs : SmartPrint.t list) : SmartPrint.t =
  match docs with
  | [] -> !^ "tt"
  | [doc] -> doc
  | _ :: _ :: _ -> nest (brakets (separate (!^ "," ^^ space) docs))

let primitive_tuple_pattern (docs : SmartPrint.t list) : SmartPrint.t =
  match docs with
  | [] -> !^ "_"
  | [doc] -> doc
  | _ :: _ :: _ -> nest (!^ "'" ^-^ brakets (separate (!^ "," ^^ space) docs))

let primitive_tuple_type (docs : SmartPrint.t list) : SmartPrint.t =
  match docs with
  | [] -> !^ "unit"
  | [doc] -> doc
  | _ :: _ :: _ -> nest (brakets (separate (space ^^ !^ "**" ^^ space) docs))

let to_string (doc : SmartPrint.t) : string =
  SmartPrint.to_string 80 2 doc

let set : SmartPrint.t =
  !^ "Set"
