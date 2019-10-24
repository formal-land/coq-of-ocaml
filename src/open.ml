open Sexplib.Std
open SmartPrint

type t = Name.t list
  [@@deriving sexp]

let of_ocaml (path : Path.t) : t =
  let o = PathName.of_path path in
  o.PathName.path @ [o.PathName.base]

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ separate (!^ ".") (List.map Name.to_coq o) ^-^ !^ ".")
