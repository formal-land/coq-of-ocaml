(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open Typedtree
open Sexplib.Std
open SmartPrint

type t =
  | Access of t * Name.t
  | PathName of PathName.t
  [@@deriving sexp]

let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

let rec of_path (env : Env.t) (loc : Loc.t) (path : Path.t) : t =
  PathName (PathName.of_path loc path)

let rec to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, field) ->
    parens (!^ "projT2" ^^ to_coq path) ^-^ parens (Name.to_coq field)
  | PathName path_name -> PathName.to_coq path_name
