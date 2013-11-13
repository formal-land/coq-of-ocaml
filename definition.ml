open Typedtree

type t = {
  name : Name.t;
  free_type_vars : Name.t list;
  args : (Name.t * Type.t) list;
  body : Exp.t * Type.t;
  is_rec : bool}

let of_structure_item (item : structure_item) : t =
  match item.str_desc with
  | Tstr_value (rec_flag, [pattern, e]) ->
    let name = Name.of_pattern pattern in
    let schema = Schema.of_expression e in
    let free_type_vars = schema.Schema.variables in
    let (args_type, body_type) = Type.open_function schema.Schema.typ in
    let (args_name, body_exp) = Exp.open_function (Exp.of_expression e) in
    let is_rec = match rec_flag with
      | Asttypes.Nonrecursive -> false
      | Asttypes.Recursive -> true
      | _ -> failwith "recursivity flag not handled" in
    {
      name = name;
      free_type_vars = free_type_vars;
      args = List.combine args_name args_type;
      body = (body_exp, body_type);
      is_rec = is_rec}
  | _ -> failwith "structure item not handled"

let pp (f : Format.formatter) (def : t) : unit =
  if def.is_rec then
    Format.fprintf f "Fixpoint@ "
  else
    Format.fprintf f "Definition@ ";
  Name.pp f def.name;
  (match def.free_type_vars with
  | [] -> ()
  | xs ->
    Format.fprintf f "@ {";
    List.iter (fun x -> Name.pp f x; Format.fprintf f "@ ") xs;
    Format.fprintf f ":@ Type}");
  List.iter (fun (x, t) ->
    Format.fprintf f "@ (";
    Name.pp f x;
    Format.fprintf f "@ :@ ";
    Type.pp f t;
    Format.fprintf f ")") def.args;
  Format.fprintf f "@ :@ ";
  Type.pp f (snd def.body);
  Format.fprintf f "@ :=@ ";
  Exp.pp f false (fst def.body);
  Format.fprintf f "."
