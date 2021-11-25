type t = (Name.t * Kind.t) list
(** A list of type variables together with their kinds. *)

(** For debugging. *)
let to_string (env : t) : string =
  "[ "
  ^ List.fold_left
      (fun s (name, k) ->
        s ^ ", " ^ Name.to_string name ^ " : " ^ Kind.to_string k)
      "" env
  ^ " ]"

(** Union preserves the ordering of the first argument. *)
let rec union (env1 : t) (env2 : t) : t =
  match env1 with
  | [] -> env2
  | (name, kind) :: env -> (
      match List.assoc_opt name env2 with
      | None -> (name, kind) :: union env env2
      | Some kind' ->
          let env2 = List.remove_assoc name env2 in
          let kind = Kind.union kind kind' in
          (name, kind) :: union env env2)

(** Union on a list of environments. *)
let unions (envs : t list) : t = List.fold_left union [] envs

(** Project an environment on a certain list of names, using the order of these
    names. *)
let reorg (names : Name.t list) (env : t) : t =
  names
  |> List.filter_map (fun name ->
         match List.assoc_opt name env with
         | None -> None
         | Some kind -> Some (name, kind))

let rec group_by_kind_aux (env : t) (kind : Kind.t) :
    (Kind.t * Name.t list) list * Name.t list * Kind.t =
  match env with
  | [] -> ([], [], kind)
  | [ (name, k) ] -> ([], [ name ], k)
  | (name, k) :: ls ->
      let ls, names, k' = group_by_kind_aux ls k in
      if k = k' then (ls, names @ [ name ], k)
      else ((k', names) :: ls, [ name ], k)

(** Group the names by kind, so that the printing will be nicer. *)
let group_by_kind (env : t) : (Kind.t * Name.t list) list =
  match env with
  | [] -> []
  | [ (name, k) ] -> [ (k, [ name ]) ]
  | (name, k) :: ls ->
      let ls, names, k' = group_by_kind_aux ls k in
      if k = k' then (k, names @ [ name ]) :: ls
      else if List.length names = 0 then (k, [ name ]) :: ls
      else (k, [ name ]) :: (k', names) :: ls

(** Remove a list of names from an environment. *)
let remove (keys : Name.t list) (env : t) : t =
  env |> List.filter (fun (name, _) -> not (List.mem name keys))

(** Only keep a certain list of names from the environment. *)
let keep_only (keys : Name.t list) (env : t) : t =
  env |> List.filter (fun (name, _) -> List.mem name keys)
