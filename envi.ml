type 'a t = 'a PathName.Map.t list

exception NotFound of PathName.t

let empty : 'a t = [PathName.Map.empty]

let add (x : PathName.t) (v : 'a) (env : 'a t) : 'a t =
  match env with
  | map :: env -> PathName.Map.add x v map :: env
  | [] -> failwith "The environment must be a non-empty list."

let add_name (x : Name.t) (v : 'a) (env : 'a t) : 'a t =
  add (PathName.of_name [] x) v env

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

let rec find (x : BoundName.t) (env : 'a t) : 'a =
  let map =
    try List.nth env x.BoundName.depth with
    | Failure "nth" -> raise Not_found in
  PathName.Map.find x.BoundName.path_name map

let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
  let mem (x : PathName.t) : bool =
    try let _ = depth x env in true with NotFound _ -> false in
  let prefix_n s n =
    if n = 0 then
      Name.of_string s
    else
      Name.of_string @@ Printf.sprintf "%s_%d" s n in
  let rec first_n (n : int) : int =
    if mem (PathName.of_name [] @@ prefix_n prefix n) then
      first_n (n + 1)
    else
      n in
  let x = prefix_n prefix (first_n 0) in
  (x, add_name x v env)

let map (env : 'a t) (f : 'a -> 'b) : 'b t =
  List.map (fun map -> PathName.Map.map f map) env

let open_module (env : 'a t) : 'a t =
  PathName.Map.empty :: env

let close_module (env : 'a t) (lift : 'a -> Name.t -> 'a) (name : Name.t)
  : 'a t =
  match env with
  | map1 :: map2 :: env ->
    PathName.Map.fold (fun x v map2 ->
      let x = { x with PathName.path = name :: x.PathName.path } in
      PathName.Map.add x (lift v name) map2)
      map1 map2
      :: env
  | _ -> failwith "At least one module should be opened."