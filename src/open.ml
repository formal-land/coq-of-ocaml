open SmartPrint

type t = PathName.t

let of_ocaml (path : Path.t) : t Monad.t =
  PathName.of_path_with_convert false path

(** Pretty-print an open construct to Coq. *)
let to_coq (o : t): SmartPrint.t =
  nest (!^ "Import" ^^ PathName.to_coq o ^-^ !^ ".")
