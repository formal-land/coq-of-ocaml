(** Local identifiers, used for variable names in patterns for example. *)
open Typedtree
open SmartPrint

(** Just a [string] (no freshness counter for now). *)
type t = string

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

let pp (x : t) : SmartPrint.t =
  single_quotes (!^ x)

(** Import an OCaml identifier. *)
let of_ident (i : Ident.t) : t =
  i.Ident.name

(** Lift a [string] to an identifier. *)
let of_string (s : string) : t =
  s

(** Generate a fresh name from a given [prefix] using an internal counter. *)
(*let unsafe_fresh : string -> t =
  let counters : int Map.t ref = ref Map.empty in
  fun prefix ->
    if not (Map.mem prefix !counters) then
      counters := Map.add prefix 0 !counters;
    let n = Map.find prefix !counters in
    counters := Map.add prefix (n + 1) !counters;
    Printf.sprintf "%s_%d" prefix n*)

(** Pretty-print a name to Coq. *)
let to_coq (x : t) : SmartPrint.t =
  !^ x