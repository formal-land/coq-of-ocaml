open SmartPrint

type t =
  | None
  | CoqRec
  | FreeRec

let pp (attr : t) : SmartPrint.t =
  match attr with
  | None -> !^ "@."
  | CoqRec -> !^ "@coq_rec"
  | FreeRec -> !^ "@free_rec"

let of_attributes (attrs : Typedtree.attributes) : t =
  let attrs : string list = List.map (fun attr -> (fst attr).Asttypes.txt) attrs in
  if List.mem "coq_rec" attrs && List.mem "free_rec" attrs then
    failwith "There cannot be both \"@coq_rec\" and \"@free_rec\" attributes." else
  if List.mem "coq_rec" attrs then
    CoqRec
  else if List.mem "free_rec" attrs then
    FreeRec
  else
    None