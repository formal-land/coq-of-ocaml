open SmartPrint

(** A non-empty list of maps. *)
type 'a t = 'a PathName.Map.t list

let pp (pp_v : 'a -> SmartPrint.t) (env : 'a t) : SmartPrint.t =
  List.map PathName.Map.bindings env |>
  List.concat |>
  OCaml.list (fun (x, v) ->
    nest (PathName.pp x ^^ !^ ":" ^^ pp_v v))

let empty : 'a t = [PathName.Map.empty]

let add (x : PathName.t) (v : 'a) (env : 'a t) : 'a t =
  match env with
  | map :: env -> PathName.Map.add x v map :: env
  | [] -> failwith "The environment must be a non-empty list."

let rec find (x : PathName.t) (env : 'a t) : 'a =
  match env with
  | map :: env ->
    (try PathName.Map.find x map with
    | Not_found -> find x env)
  | [] -> raise Not_found

let open_module (env : 'a t) : 'a t =
  PathName.Map.empty :: env

let close_module (env : 'a t) (name : string) : 'a t =
  match env with
  | map1 :: map2 :: env ->
    PathName.Map.fold (fun x v map ->
      let { PathName.path = path; base = base } = x in
      PathName.Map.add { PathName.path = name :: path; base = base } v map)
      map1 map2
      :: env
  | _ -> failwith "At least one module should be opened."