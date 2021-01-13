open Monad.Notations
type t = (Name.t * Kind.t) list

let to_string (env : t) : string =
  "[ " ^
  (List.fold_left (fun s (name, k) ->
       s ^ ", " ^ (Name.to_string name) ^ " : " ^ (Kind.to_string k)
     )
     "" env)
  ^ " ]"

(* Union preserves the ordering of the first argument *)
let rec union (env1 : t) (env2 : t) : t =
  match env1 with
  | [] -> env2
  | (name, kind) :: env ->
    match List.assoc_opt name env2 with
    | None ->
      (name, kind) :: union env env2
    | Some kind' ->
      let env2 = List.remove_assoc name env2 in
      let kind = Kind.union kind kind' in
      (* let env = (name, kind) :: (List.remove_assoc name env) in *)
      (name, kind) :: union env env2

let merge (env : t list) : t =
  match env with
  | [] -> []
  | x :: xs -> List.fold_left (fun acc y -> union acc y) x xs

let reorg (names : Name.t list) (env : t): t =
  List.fold_left (fun acc name ->
      match List.assoc_opt name env with
      | None -> acc
      | Some kind -> (name, kind) :: acc
    ) [] names
  |> List.rev

let rec group_by_kind_aux
    (m : t)
    (kind : Kind.t)
  : (Kind.t * Name.t list) list * Name.t list * Kind.t =
  match m with
  | [] -> ([], [], kind)
  | [(name, k)] -> ([], [name], k)
  | (name, k) :: ls ->
    let (ls, names, k') = group_by_kind_aux ls k in
    if k = k'
    then (ls, names @ [name], k)
    else ((k', names) :: ls, [name], k)

let group_by_kind
    (m : t)
  : ((Kind.t * Name.t list) list) =
  match m with
  | [] -> []
  | [ (name,k) ] -> [k, [name]]
  | (name, k) :: ls ->
    let (ls, names, k') = group_by_kind_aux ls k in
    if k = k'
    then ((k, names @ [name]) :: ls)
    else
      if List.length names = 0
      then ((k, [name]) :: ls)
      else ((k, [name]) :: (k', names) :: ls)

let rec remove (key : Name.t) (varenv : t) : t =
  match varenv with
  | [] -> []
  | (name, kind) :: varenv ->
    if name = key
    then varenv
    else (name, kind) :: remove key varenv

let rec remove_many (keys : Name.t list) (varenv : t) : t =
  List.fold_left (fun varenv key -> remove key varenv) varenv keys

let rec assq_get (x : 'a) (l : ('a * 'b) list) : ('a * 'b) option =
  match l with
  | [] -> None
  | (a, b) :: xs ->
    if a = x
    then Some (a, b)
    else assq_get x xs

let rec keep_only (keys : Name.t list) (varenv : t) : t =
  List.fold_left (fun l key ->
      match assq_get key varenv with
      | Some x -> x :: l
      | None -> l
    ) [] keys |> List.rev
