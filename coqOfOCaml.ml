module Exp = struct
  open Typedtree
  open Asttypes
  
  type t =
    | Constant of constant
    | Variable of Path.t * Longident.t loc * Types.value_description
    | Tuple of t list
    | Apply of t * t list
    | Function of pattern * t
    | Let of pattern * t * t
  
  let rec of_expression (e : expression) : t =
    match e.exp_desc with
    | Texp_ident (path, loc, description) -> Variable (path, loc, description)
    | Texp_constant constant -> Constant constant
    | Texp_let (Nonrecursive, [x, e1], e2) -> Let (x, of_expression e1, of_expression e2)
    | Texp_function (_, [x, e], _) -> Function (x, of_expression e)
    | Texp_apply (e_f, e_xs) -> Apply (of_expression e_f, List.map (fun (_, e_x, _) ->
      match e_x with
      | Some e_x -> of_expression e_x
      | None -> failwith "expected an argument") e_xs)
    | Texp_tuple es -> Tuple (List.map of_expression es)
    | _ -> failwith "expression not handled"
end

module Definition = struct
  open Typedtree
  
  type t = pattern * Exp.t
  
  let of_structure_item (item : structure_item) : t =
    match item.str_desc with
    | Tstr_value (Asttypes.Nonrecursive, [pattern, e]) -> (pattern, Exp.of_expression e)
    | _ -> failwith "structure item not handled"
end

module Definitions = struct
  open Typedtree
  
  type t = Definition.t list
  
  let of_structure (structure : structure) : t =
    List.map Definition.of_structure_item structure.str_items
end

let parse (file_name : string) : Typedtree.structure =
  let env = Env.initial in
  let input = Pparse.preprocess file_name in
  let input = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  let (structure, _, _) = Typemod.type_toplevel_phrase env input in
  structure

let parse_and_print (file_name : string) : unit =
  Printf.printf "Parsing %s:\n" file_name;
  let structure = parse file_name in
  let definitions = Definitions.of_structure structure in
  Printf.printf "number of definitions: %d\n" (List.length definitions);
  Printtyped.implementation Format.std_formatter structure

let main () =
  Arg.parse [] parse_and_print "Usage: ..."

;;main ()
