open SmartPrint

let parens (b : bool) (doc : SmartPrint.t) : SmartPrint.t =
  if b then
    parens doc
  else
    doc

let rec to_coq_n_underscores (n : int) : SmartPrint.t list =
  if n = 0 then
    []
  else
    (!^ "_") :: to_coq_n_underscores (n - 1)

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

let primitive_tuple_infer (n : int) : SmartPrint.t =
  match to_coq_n_underscores n with
  | [] -> !^ "tt"
  | [_] -> !^ "_"
  | n_underscores -> brakets (separate (!^ "," ^^ space) n_underscores)

let to_string (doc : SmartPrint.t) : string =
  SmartPrint.to_string 80 2 doc

let set : SmartPrint.t =
  !^ "Set"

let args (with_args : bool) : SmartPrint.t =
  if with_args then
    !^ "`{FArgs}"
  else
    empty

let rec typ_arity (arity : int) : SmartPrint.t =
  match arity with
  | 0 -> set
  | arity -> set ^^ !^ "->" ^^ (typ_arity (arity - 1))
