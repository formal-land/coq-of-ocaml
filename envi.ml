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

module Segment = struct
  type 'a t = {
    opens : Name.t list list;
    names : (Visibility.t * 'a) PathName.Map.t }

  let pp (segment : 'a t) : SmartPrint.t =
    !^ "open" ^^ OCaml.list (fun path ->
      separate (!^ ".") (List.map Name.pp path))
      segment.opens ^^
    OCaml.list (fun (x, (visibility, _)) ->
      Visibility.pp visibility ^^ PathName.pp x)
      (PathName.Map.bindings segment.names)

  let cardinal (segment : 'a t) : int =
    PathName.Map.cardinal segment.names

  let empty : 'a t = {
    opens = [];
    names = PathName.Map.empty }

  let add (x : PathName.t) (visibility : Visibility.t) (v : 'a)
    (segment : 'a t) : 'a t =
    { segment with names = PathName.Map.add x (visibility, v) segment.names }

  let mem (x : PathName.t) (segment : 'a t) : bool =
    PathName.Map.mem x segment.names

  let find (x : PathName.t) (segment : 'a t) : Visibility.t * 'a =
    PathName.Map.find x segment.names

  let map (f : 'a -> 'b) (segment : 'a t) : 'b t =
    { segment with names =
      PathName.Map.map (fun (visibility, v) -> (visibility, f v))
        segment.names }

  let merge (segment1 : 'a t) (segment2 : 'a t) (prefix : Name.t -> 'a -> 'a)
    (module_name : Name.t) : 'a t =
    PathName.Map.fold (fun x (visibility, v) segment2 ->
      let x = { x with PathName.path = module_name :: x.PathName.path } in
      add x visibility (prefix module_name v) segment2)
      segment1.names segment2
end

type 'a t = 'a Segment.t list

let pp (env : 'a t) : SmartPrint.t =
  OCaml.list Segment.pp env

exception NotFound of PathName.t

let rec size (env : 'a t) : int =
  match env with
  | [] -> 0
  | segment :: env -> Segment.cardinal segment + size env

let empty : 'a t = [Segment.empty]

let add (x : PathName.t) (visibility : Visibility.t) (v : 'a) (env : 'a t)
  : 'a t =
  match env with
  | segment :: env -> Segment.add x visibility v segment :: env
  | [] -> failwith "The environment must be a non-empty list."

let rec depth (x : PathName.t) (env : 'a t) : int =
  match env with
  | segment :: env ->
    if Segment.mem x segment then
      0
    else
      1 + depth x env
  | [] -> raise (NotFound x)

let bound_name (x : PathName.t) (env : 'a t) : BoundName.t =
  { BoundName.path_name = x; depth = depth x env }

let rec find (x : BoundName.t) (env : 'a t) (open_lift : 'a -> 'a) : 'a =
  let segment =
    try List.nth env x.BoundName.depth with
    | Failure "nth" -> raise Not_found in
  let rec iterate_open_lift v n =
    if n = 0 then
      v
    else
      iterate_open_lift (open_lift v) (n - 1) in
  let (_, v) = Segment.find x.BoundName.path_name segment in
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
  List.map (Segment.map f) env

let enter_module (env : 'a t) : 'a t =
  Segment.empty :: env

let leave_module (env : 'a t) (prefix : Name.t -> 'a -> 'a)
  (module_name : Name.t) : 'a t =
  match env with
  | segment1 :: segment2 :: env ->
    Segment.merge segment1 segment2 prefix module_name :: env
  | _ -> failwith "You should have entered in at least one module."

let open_module (env : 'a t) (module_name : PathName.t) : 'a t =
  failwith "TODO"