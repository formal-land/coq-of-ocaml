(** Local identifiers, used for variable names in patterns for example. *)
open Typedtree
open SmartPrint

(** Just a [string] (no freshness counter for now). *)
type t = string

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
module Map = Map.Make (struct type t = t' let compare = compare end)

(** Import an OCaml identifier. *)
let of_ident (i : Ident.t) : t =
  i.Ident.name

(** Lift a [string] to an identifier. *)
let of_string (s : string) : t =
  s

(** Generate a fresh name from a given [prefix] using an internal counter. *)
let unsafe_fresh : string -> t =
  let counters : int Map.t ref = ref Map.empty in
  fun prefix ->
    if not (Map.mem prefix !counters) then
      counters := Map.add prefix 0 !counters;
    let n = Map.find prefix !counters in
    counters := Map.add prefix (n + 1) !counters;
    Printf.sprintf "%s_%d" prefix n

(*
(** Generate a fresh name from a given [prefix] which is not in [env]. *)
let fresh (prefix : string) (env : Set.t) : t * Set.t =
  let prefix_n s n =
    if n = 0 then s
    else Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if Set.mem (prefix_n prefix n) env then first_n (n + 1)
    else n in
  let s = prefix_n prefix (first_n 0) in
  (s, Set.add s env)
*)

(** Pretty-print a name. *)
let pp (name : t) : SmartPrint.t =
  !^ name