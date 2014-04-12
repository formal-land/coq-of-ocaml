open SmartPrint

module Visibility = struct
  type t =
    | Global
    | Local

  let pp (visibility : t) : SmartPrint.t =
    match visibility with
    | Global -> !^ "Global"
    | Local -> !^ "Local"
end

(** If the boolean is true, the name is only local. *)
type 'a t = (Visibility.t * 'a) PathName.Map.t list

let pp (d : 'a t) : SmartPrint.t =
  d |> OCaml.list (fun map ->
    PathName.Map.bindings map |> OCaml.list (fun (x, (visibility, _)) ->
      Visibility.pp visibility ^^ PathName.pp x))

exception NotFound of PathName.t

let rec size (env : 'a t) : int =
  match env with
  | [] -> 0
  | map :: env -> PathName.Map.cardinal map + size env

let empty : 'a t = [PathName.Map.empty]

let add (x : PathName.t) (visibility : Visibility.t) (v : 'a) (env : 'a t) : 'a t =
  match env with
  | map :: env -> PathName.Map.add x (visibility, v) map :: env
  | [] -> failwith "The environment must be a non-empty list."

(*let add_name (x : Name.t) (visibility : Visibility.t) (v : 'a) (env : 'a t) : 'a t =
  add (PathName.of_name [] x) visibility v env*)

let rec depth (x : PathName.t) (env : 'a t) : int =
  match env with
  | map :: env ->
    if PathName.Map.mem x map then
      0
    else
      1 + depth x env
  | [] -> raise (NotFound x)

let bound_name (x : PathName.t) (env : 'a t) : BoundName.t =
  { BoundName.path_name = x; depth = depth x env }

let rec find (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  let map =
    try List.nth env x.BoundName.depth with
    | Failure "nth" -> raise Not_found in
  let rec iterate_open_lift v n =
    if n = 0 then
      v
    else
      iterate_open_lift (open_lift v) (n - 1) in
  let (_, v) = PathName.Map.find x.BoundName.path_name map in
  iterate_open_lift v x.BoundName.depth

let mem (x : PathName.t) (env : 'a t) : bool =
  try let _ = depth x env in true with NotFound _ -> false

(** Add a fresh local name beginning with [prefix] in [env]. *)
let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if mem (PathName.of_name [] @@ prefix_n prefix n) env then
      first_n (n + 1)
    else
      n in
  let x = prefix_n prefix (first_n 0) in
  (x, add (PathName.of_name [] x) Visibility.Local v env)

let map (env : 'a t) (f : 'a -> 'b) : 'b t =
  env |> List.map (fun map ->
    PathName.Map.map (fun (visibility, v) -> (visibility, f v)) map)

let open_module (env : 'a t) : 'a t =
  PathName.Map.empty :: env

let close_module (env : 'a t) (lift : 'a -> Name.t -> 'a) (name : Name.t)
  : 'a t =
  match env with
  | map1 :: map2 :: env ->
    PathName.Map.fold (fun x (visibility, v) map2 ->
      let x = { x with PathName.path = name :: x.PathName.path } in
      PathName.Map.add x (visibility, lift v name) map2)
      map1 map2
      :: env
  | _ -> failwith "At least one module should be opened."