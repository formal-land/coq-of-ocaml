open SmartPrint

module Segment = struct
  type path = Name.t list

  type 'a t = {
    opens : path list;
    names : 'a PathName.Map.t }

  let cardinal (segment : 'a t) : int =
    PathName.Map.cardinal segment.names

  let empty : 'a t = {
    opens = [[]]; (** By default we open the empty path. *)
    names = PathName.Map.empty }

  let add (x : PathName.t) (v : 'a) (segment : 'a t) : 'a t =
    { segment with names = PathName.Map.add x v segment.names }

  let find_opt (x : PathName.t) (segment : 'a t) : 'a option =
    PathName.Map.find_opt x segment.names

  let map (f : 'a -> 'b) (segment : 'a t) : 'b t =
    { segment with names = PathName.Map.map f segment.names }

  (** Close [segment1] by merging it into [segment2] while prefixing it with [module_name]. *)
  let close_and_merge (segment1 : 'a t) (segment2 : 'a t) (module_name : Name.t) : 'a t =
    PathName.Map.fold
      (fun x v segment2 ->
        let x = { x with PathName.path = module_name :: x.PathName.path } in
        add x v segment2
      )
      segment1.names
      segment2

  let open_module (segment : 'a t) (module_name : path) : 'a t =
    { segment with opens = module_name :: segment.opens }
end

type 'a t = 'a Segment.t list

let rec size (env : 'a t) : int =
  match env with
  | [] -> 0
  | segment :: env -> Segment.cardinal segment + size env

let empty : 'a t = [Segment.empty]

let add (x : PathName.t) (v : 'a) (env : 'a t) : 'a t =
  match env with
  | segment :: env -> Segment.add x v segment :: env
  | [] -> failwith "The environment must be a non-empty list."

let rec find_first (f : 'a -> 'b option) (l : 'a list) : 'b option =
  match l with
  | [] -> None
  | x :: l ->
    (match f x with
    | None -> find_first f l
    | y -> y)

(** Returns the depth of the definition in the segments and the path name as if
    there were no [open]. *)
let rec depth (x : PathName.t) (env : 'a t) : (PathName.t * int * 'a) option =
  match env with
  | segment :: env ->
    begin match Segment.find_opt x segment with
    | Some y -> Some (x, 0, y)
    | None ->
      segment.Segment.opens |> find_first (fun path ->
        let x = { x with PathName.path = path @ x.PathName.path } in
        match depth x env with
        | None -> None
        | Some (x, d, y) -> Some (x, d + 1, y)
      )
    end
  | [] -> None

let bound_name (loc : Loc.t) (x : PathName.t) (env : 'a t) : BoundName.t * 'a =
  match depth x env with
  | Some (x, d, y) -> ({ BoundName.path_name = x; depth = d }, y)
  | None ->
    let message = Pp.to_string (PathName.to_coq x) ^ " not found." in
    Error.raise loc message

let mem (x : PathName.t) (env : 'a t) : bool =
  match depth x env with
  | Some _ -> true
  | None -> false

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
  (x, add (PathName.of_name [] x) v env)

let map (env : 'a t) (f : 'a -> 'b) : 'b t =
  List.map (Segment.map f) env

let enter_module (env : 'a t) : 'a t =
  Segment.empty :: env

let leave_module (env : 'a t) (module_name : Name.t) : 'a t =
  match env with
  | segment1 :: segment2 :: env ->
    Segment.close_and_merge segment1 segment2 module_name :: env
  | _ -> failwith "You should have entered in at least one module."

let open_module (env : 'a t) (module_name : Name.t list) : 'a t =
  match env with
  | segment :: env -> Segment.open_module segment module_name :: env
  | _ -> failwith "You should have entered in at least one module."
