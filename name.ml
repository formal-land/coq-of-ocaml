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
  	if Map.mem prefix !counters then (
  	  let n = Map.find prefix !counters in
  	  counters := Map.add  prefix (n + 1) !counters;
  	  Printf.sprintf "%s_%d" prefix n)
  	else (
  	  counters := Map.add prefix (-1) !counters;
  	  Printf.sprintf "%s_0" prefix)

let pp (f : Format.formatter) (n : t) : unit =
  Format.fprintf f "%s" n