open Typedtree
open SmartPrint

type t = Name.t list

let pp (o : t) : SmartPrint.t =
  nest (!^ "Open" ^^ separate (!^ ".") (List.map Name.pp o))

let of_ocaml (loc : Loc.t) (path : Path.t) : t =
  let o = PathName.of_path loc path in
  o.PathName.path @ [o.PathName.base]

let update_env (o : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  FullEnvi.open_module o env

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ separate (!^ ".") (List.map Name.pp o) ^-^ !^ ".")
