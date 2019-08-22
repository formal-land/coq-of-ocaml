open Sexplib.Std
open SmartPrint

type t = {
  path_name : PathName.t;
  depth : int }
  [@@deriving sexp]

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.path_name
