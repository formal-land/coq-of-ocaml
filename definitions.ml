open Typedtree

type t = Definition.t list

let of_structure (structure : structure) : t =
  List.map Definition.of_structure_item structure.str_items

let pp (f : Format.formatter) (defs : t) : unit =
  Pp.sep_by defs (fun _ -> Format.fprintf f "@\n@\n") (fun def -> Definition.pp f def)
