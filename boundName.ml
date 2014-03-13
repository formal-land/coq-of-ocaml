open SmartPrint

type t = {
  path_name : PathName.t;
  depth : int }

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)

let pp (x : t) : SmartPrint.t =
  PathName.pp x.path_name ^-^ !^ "/" ^-^ OCaml.int x.depth

let open_lift (x : t) : t =
  { x with depth = x.depth + 1 }

let close_lift (x : t) (name : Name.t) : t =
  if x.depth = 0 then
    { x with path_name = { x.path_name with
      PathName.path = name :: x.path_name.PathName.path } }
  else
    { x with depth = x.depth - 1 }

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (
    x.path_name.PathName.path @ [x.path_name.PathName.base]))