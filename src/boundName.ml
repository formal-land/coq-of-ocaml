open SmartPrint

type t = {
  path_name : PathName.t;
  depth : int }

let pp (x : t) : SmartPrint.t =
  PathName.pp x.path_name ^-^ !^ "/" ^-^ OCaml.int x.depth

let depth_lift (x : t) : t =
  { x with depth = x.depth + 1 }

let leave_prefix (name : Name.t) (x : t) : t =
  if x.depth = 0 then
    { x with path_name = { x.path_name with
      PathName.path = name :: x.path_name.PathName.path } }
  else
    { x with depth = x.depth - 1 }

let to_coq (x : t) : SmartPrint.t =
  PathName.to_coq x.path_name