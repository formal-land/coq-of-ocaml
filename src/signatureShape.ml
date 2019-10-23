(** The shape of a signature to simplify comparisons. Two signatures are considered
    similar if they have the same shape. The shape only contains the names of the
    value and type definitions (without the values of the types for example), and such
    recursively for each sub-module. Basically, shapes are trees of strings. *)
open SmartPrint

type t = unit Tree.t

let rec of_signature (signature : Types.signature) : t =
  let rec of_signature_item (signature_item : Types.signature_item) =
    match signature_item with
    | Sig_value (ident, _) | Sig_type (ident, _, _) ->
      Some (Tree.Item (Name.of_ident ident, ()))
    | Sig_typext _ | Sig_modtype _ | Sig_class _ | Sig_class_type _ -> None
    | Sig_module (ident, module_declaration, _) ->
      let name = Name.of_ident ident in
      begin match module_declaration.md_type with
      | Mty_signature signature -> Some (Tree.Module (name, of_signature signature))
      | _ -> None
      end in
  signature |> Util.List.filter_map of_signature_item

let rec are_equal (shape1 : t) (shape2 : t) : bool =
  (* To speedup the comparison, with first compare the lengths. *)
  List.length shape1 = List.length shape2 &&
  let compare_items = fun item1 item2 ->
    match (item1, item2) with
    | (Tree.Module (name1, _) | Tree.Item (name1, ())),
      (Tree.Module (name2, _) | Tree.Item (name2, ())) ->
      String.compare name1 name2 in
  let shape1 = shape1 |> List.sort compare_items in
  let shape2 = shape2 |> List.sort compare_items in
  List.for_all2
    (fun item1 item2 ->
      match (item1, item2) with
      | Tree.Module (name1, shape1), Tree.Module (name2, shape2) -> name1 = name2 && are_equal shape1 shape2
      | Tree.Item (name1, ()), Tree.Item (name2, ()) -> name1 = name2
      | Tree.Module _, Tree.Item _ | Tree.Item _, Tree.Module _ -> false
    )
    shape1
    shape2

let rec pretty_print (shape : t) : SmartPrint.t =
  shape |> OCaml.list (fun item ->
    match item with
    | Tree.Item (name, _) -> Name.to_coq name
    | Tree.Module (name, shape) -> OCaml.tuple [Name.to_coq name; pretty_print shape]
  )
