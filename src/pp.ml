open SmartPrint

let parens (b : bool) (doc : SmartPrint.t) : SmartPrint.t =
  if b then
    parens doc
  else
    doc

let to_string (doc : SmartPrint.t) : string =
  SmartPrint.to_string 80 2 doc

let set : SmartPrint.t =
  !^ "Set"
