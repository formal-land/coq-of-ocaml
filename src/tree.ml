open SmartPrint
(** We use the trees to represent abstract type parameters of signatures.  *)

open Monad.Notations

type 'a item = Item of string * 'a | Module of string * 'a t
and 'a t = 'a item list

let rec map (f : 'a -> 'b) (tree : 'a t) : 'b t =
  let map_item (item : 'a item) : 'b item =
    match item with
    | Item (name, x) -> Item (name, f x)
    | Module (name, tree) -> Module (name, map f tree)
  in
  tree |> List.map map_item

let rec map_at (tree : 'a t) (path : string list) (f : 'a -> 'a) : 'a t =
  match path with
  | [] -> tree
  | head :: tail ->
      tree
      |> List.map (fun item ->
             match (item, tail) with
             | Item (name, x), [] when name = head -> Item (name, f x)
             | Item _, _ -> item
             | Module (name, tree), _ when name = head ->
                 Module (name, map_at tree tail f)
             | Module _, _ -> item)

let rec mapi_aux (prefix : string list) (f : string list -> 'a -> 'b Monad.t)
    (tree : 'a t) : 'b t Monad.t =
  let map_item (item : 'a item) : 'b item Monad.t =
    match item with
    | Item (name, x) ->
        let* v = f (List.rev (name :: prefix)) x in
        return (Item (name, v))
    | Module (name, tree) ->
        let* tree = mapi_aux (name :: prefix) f tree in
        return (Module (name, tree))
  in
  tree |> Monad.List.map map_item

let mapi (f : string list -> 'a -> 'b Monad.t) (tree : 'a t) : 'b t Monad.t =
  mapi_aux [] f tree

let rec flatten_aux (prefix : string list) (tree : 'a t) :
    (string list * 'a) list =
  tree
  |> List.concat_map (fun item ->
         match item with
         | Item (name, x) ->
             let path = List.rev (name :: prefix) in
             [ (path, x) ]
         | Module (name, tree) -> flatten_aux (name :: prefix) tree)

let flatten (tree : 'a t) : (string list * 'a) list = flatten_aux [] tree

let rec pp (pp_a : 'a -> SmartPrint.t option) (tree : 'a t) : SmartPrint.t =
  let pp_item (item : 'a item) : SmartPrint.t =
    match item with
    | Item (name, value) -> (
        !^name
        ^-^ match pp_a value with None -> empty | Some doc -> !^":" ^^ doc)
    | Module (name, tree) -> !^name ^-^ !^":" ^^ pp pp_a tree
  in
  OCaml.list pp_item tree
