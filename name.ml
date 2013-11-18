open Typedtree

type t = string

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

let of_ident (i : Ident.t) : t =
  i.Ident.name

let fresh : string -> t =
  let counters : int Map.t ref = ref Map.empty in
  fun prefix ->
    if not (Map.mem prefix !counters) then
      counters := Map.add prefix 0 !counters;
    let n = Map.find prefix !counters in
    counters := Map.add prefix (n + 1) !counters;
    Printf.sprintf "%s_%d" prefix n

let pp (f : Format.formatter) (name : t) : unit =
  Format.fprintf f "%s" name