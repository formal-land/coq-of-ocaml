open Sexplib.Std
open SmartPrint

type 'a item =
  | Item of Name.t * 'a
  | Module of Name.t * 'a t

and 'a t = 'a item list
  [@@deriving sexp]

let rec map (f : 'a -> 'b) (tree : 'a t) : 'b t =
  let map_item (item : 'a item) : 'b item =
    match item with
    | Item (name, x) -> Item (name, f x)
    | Module (name, tree) -> Module (name, map f tree) in
  tree |> List.map map_item

let rec map_at (tree : 'a t) (path_name : PathName.t) (f : 'a -> 'a) : 'a t =
  let (head, tail) = PathName.get_head_and_tail path_name in
  tree |> List.map (fun item ->
    match item with
    | Item (name, x) ->
      if name = head then
        Item (name, f x)
      else
        item
    | Module (name, tree) ->
      match tail with
      | None -> item
      | Some path_name -> Module (name, map_at tree path_name f)
  )

let rec flatten_aux (prefix : Name.t list) (tree : 'a t) : (PathName.t * 'a) list =
  List.flatten (tree |> List.map (fun item ->
    match item with
    | Item (name, x) -> [(PathName.of_name (List.rev prefix) name, x)]
    | Module (name, tree) -> flatten_aux (name :: prefix) tree
  ))

let flatten (tree : 'a t) : (PathName.t * 'a) list =
  flatten_aux [] tree

let rec size (tree : 'a t) : int =
  tree |> List.fold_left (fun s item ->
    match item with
    | Item _ -> s + 1
    | Module (_, tree) -> s + size tree
  ) 0

let rec pp (pp_a : 'a -> SmartPrint.t option) (tree : 'a t) : SmartPrint.t =
  let pp_item (item : 'a item) : SmartPrint.t =
    match item with
    | Item (name, value) ->
      Name.to_coq name ^-^
      (match pp_a value with
      | None -> empty
      | Some doc -> !^ ":" ^^ doc)
    | Module (name, tree) -> Name.to_coq name ^-^ !^ ":" ^^ pp pp_a tree in
  OCaml.list pp_item tree
