open SmartPrint

let parens (b : bool) (d : SmartPrint.t) : SmartPrint.t =
  if b then
    parens d
  else
    d