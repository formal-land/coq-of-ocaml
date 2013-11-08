module Constant = struct
  type t =
    | Int of int
    | Char of char
    | String of string
  
  let of_constant (c : Asttypes.constant) : t =
    let open Asttypes in
    match c with
    | Const_int n -> Int n
    | Const_char c -> Char c
    | Const_string s -> String s
    | _ -> failwith "constant not handled"
  
  let pp (f : Format.formatter) (c : t) : unit =
    match c with
    | Int n -> Format.fprintf f "%d" n
    | Char c -> Format.fprintf f "%c" c
    | String s -> Format.fprintf f "%s" s
end

module Name = struct
  type t = string
  
  let of_ident (i : Ident.t) : t =
    i.Ident.name
  
  let of_pattern (p : Typedtree.pattern) : t =
    match p.Typedtree.pat_desc with
    | Typedtree.Tpat_var (i, _) -> of_ident i
    | _ -> failwith "unhandled pattern"
  
  let pp (f : Format.formatter) (n : t) : unit =
    Format.fprintf f "%s" n
end

module Ident = struct
  type t = {
    path : Name.t list;
    base : Name.t}
  
  let rec of_path (p : Path.t) : t =
    match p with
    | Path.Pident i -> { path = []; base = Name.of_ident i }
    | Path.Pdot (p, s, _) ->
      let i = of_path p in
      { path = s :: i.path; base = i.base }
    | Path.Papply _ -> failwith "application of paths not handled"
  
  let pp (f : Format.formatter) (i : t) : unit =
    List.iter (Name.pp f) i.path;
    Name.pp f i.base
end

module Exp = struct
  type t =
    | Constant of Constant.t
    | Variable of Ident.t
    | Tuple of t list
    | Apply of t * t list
    | Function of Name.t * t
    | Let of Name.t * t * t
  
  let rec of_expression (e : Typedtree.expression) : t =
    let open Typedtree in
    match e.exp_desc with
    | Texp_ident (path, _, _) -> Variable (Ident.of_path path)
    | Texp_constant constant -> Constant (Constant.of_constant constant)
    | Texp_let (Asttypes.Nonrecursive, [x, e1], e2) -> Let (Name.of_pattern x, of_expression e1, of_expression e2)
    | Texp_function (_, [x, e], _) -> Function (Name.of_pattern x, of_expression e)
    | Texp_apply (e_f, e_xs) -> Apply (of_expression e_f, List.map (fun (_, e_x, _) ->
      match e_x with
      | Some e_x -> of_expression e_x
      | None -> failwith "expected an argument") e_xs)
    | Texp_tuple es -> Tuple (List.map of_expression es)
    | _ -> failwith "expression not handled"
  
  let rec pp (f : Format.formatter) (paren : bool) (e : t) : unit =
    let open_paren () = if paren then Format.fprintf f "(" in
    let close_paren () = if paren then Format.fprintf f ")" in
    match e with
    | Constant c -> Constant.pp f c
    | Variable x -> Ident.pp f x
    | Tuple es ->
      Format.fprintf f "(";
      (match es with
      | [] -> ()
      | e :: es -> pp f true e; List.iter (fun e -> Format.fprintf f ", ";  pp f true e) es);
      Format.fprintf f ")"
    | Apply (e_f, e_xs) ->
      open_paren ();
      pp f true e_f;
      List.iter (fun e_x -> Format.fprintf f "@ "; pp f true e_x) e_xs;
      close_paren ()
    | Function (x, e) ->
      open_paren ();
      Format.fprintf f "fun@ ";
      Name.pp f x;
      Format.fprintf f "@ =>@ ";
      pp f false e;
      close_paren ()
    | Let (x, e1, e2) ->
      open_paren ();
      Format.fprintf f "let@ ";
      Name.pp f x;
      Format.fprintf f "@ =@ ";
      pp f false e1;
      Format.fprintf f "@ in@\n";
      pp f false e2;
      close_paren ()
end

module Type = struct
end

module Definition = struct
  type t = {
    name : Name.t;
    value : Exp.t}
  
  let of_structure_item (item : Typedtree.structure_item) : t =
    match item.Typedtree.str_desc with
    | Typedtree.Tstr_value (Asttypes.Nonrecursive, [pattern, e]) ->
      { name = Name.of_pattern pattern; value = Exp.of_expression e }
    | _ -> failwith "structure item not handled"
  
  let pp (f : Format.formatter) (def : t) : unit =
    Format.fprintf f "Definition@ ";
    Name.pp f def.name;
    Format.fprintf f "@ :=@ ";
    Exp.pp f false def.value;
    Format.fprintf f "."
end

module Definitions = struct
  open Typedtree
  
  type t = Definition.t list
  
  let of_structure (structure : structure) : t =
    List.map Definition.of_structure_item structure.str_items
  
  let pp (f : Format.formatter) (defs : t) : unit =
    List.iter (fun def -> Definition.pp f def; Format.fprintf f "@\n") defs
end

let parse (file_name : string) : Typedtree.structure * Types.signature =
  let env = Env.initial in
  let input = Pparse.preprocess file_name in
  let input = Pparse.file Format.str_formatter input Parse.implementation Config.ast_impl_magic_number in
  let (structure, signature, _) = Typemod.type_toplevel_phrase env input in
  (structure, signature)

let parse_and_print (file_name : string) : unit =
  Printf.printf "Parsing %s:\n" file_name;
  let (structure, signature) = parse file_name in
  let definitions = Definitions.of_structure structure in
  let f = Format.std_formatter in
  Printtyped.implementation f structure;
  Format.fprintf f "@\n";
  Printtyp.signature f signature;
  Format.fprintf f "@\n";
  Definitions.pp f definitions

let main () =
  Arg.parse [] parse_and_print "Usage: ..."

;;main ()
