open SmartPrint
open Typedtree

type t = Name.t list

let of_ocaml (open_description : open_description) : t =
  let o = PathName.of_long_ident open_description.open_txt.txt in
  o.PathName.path @ [o.PathName.base]

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ separate (!^ ".") (List.map Name.to_coq o) ^-^ !^ ".")
