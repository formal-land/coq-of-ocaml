open Typedtree

module Value = struct
  type t = {
    name : Name.t;
    free_type_vars : Name.t list;
    args : (Name.t * Type.t) list;
    body : Exp.t * Type.t;
    is_rec : bool}
  
  let pp (f : Format.formatter) (value : t) : unit =
    if value.is_rec then
      Format.fprintf f "Fixpoint@ "
    else
      Format.fprintf f "Definition@ ";
    Name.pp f value.name;
    (match value.free_type_vars with
    | [] -> ()
    | xs ->
      Format.fprintf f "@ {";
      List.iter (fun x -> Name.pp f x; Format.fprintf f "@ ") xs;
      Format.fprintf f ":@ Type}");
    List.iter (fun (x, t) ->
      Format.fprintf f "@ (";
      Name.pp f x;
      Format.fprintf f "@ :@ ";
      Type.pp f false t;
      Format.fprintf f ")")
      value.args;
    Format.fprintf f "@ :@ ";
    Type.pp f false (snd value.body);
    Format.fprintf f "@ :=@ ";
    Exp.pp f false (fst value.body);
    Format.fprintf f "."
end

module Inductive = struct
  type t = {
    name : Name.t;
    constructors : (Name.t * Type.t list) list}
  
  let pp (f : Format.formatter) (ind : t) : unit =
    Format.fprintf f "Inductive@ ";
    Name.pp f ind.name;
    Format.fprintf f "@ :=@\n";
    Format.fprintf f "|@ ";
    Format.fprintf f "@\n";
    Format.fprintf f ".";
end

type t =
  | Value of Value.t
  | Inductive of Inductive.t

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
    Value {
      Value.name = name;
      free_type_vars = free_type_vars;
      args = List.combine args_name args_type;
      body = (body_exp, body_type);
      is_rec = is_rec}
  | Tstr_type [name, _, typ] ->
    (match typ.typ_kind with
    | Ttype_variant cases -> Inductive {
      Inductive.name = Name.of_ident name;
      constructors =
        List.map (fun (constr, _, typs, _) ->
          (Name.of_ident constr, List.map (fun typ -> (Schema.of_type_expr typ.ctyp_type).Schema.typ) typs))
          cases}
    | _ -> failwith "Type definition not handled.")
  | _ -> failwith "Structure item not handled."

let pp (f : Format.formatter) (def : t) : unit =
  match def with
  | Value value -> Value.pp f value
  | Inductive ind -> Inductive.pp f ind
