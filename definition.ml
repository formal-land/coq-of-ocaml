type t = {
  name : Name.t;
  schema : Schema.t;
  value : Exp.t}

let of_structure_item (item : Typedtree.structure_item) : t =
  match item.Typedtree.str_desc with
  | Typedtree.Tstr_value (Asttypes.Nonrecursive, [pattern, e]) -> {
    name = Name.of_pattern pattern;
    schema = Schema.of_expression e;
    value = Exp.of_expression e}
  | _ -> failwith "structure item not handled"

let pp (f : Format.formatter) (def : t) : unit =
  Format.fprintf f "Definition@ ";
  Name.pp f def.name;
  (match def.schema.Schema.variables with
  | [] -> ()
  | xs ->
    Format.fprintf f "@ {";
    List.iter (fun x -> Name.pp f x; Format.fprintf f "@ ") xs;
    Format.fprintf f ":@ Type}");
  Format.fprintf f "@ :@ ";
  Type.pp f def.schema.Schema.typ;
  Format.fprintf f "@ :=@ ";
  Exp.pp f false def.value;
  Format.fprintf f "."
