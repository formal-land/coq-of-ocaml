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
  
  type t' = t
  module Set = Set.Make(struct type t = t' let compare = compare end)
end

module Ident = struct
  type t = {
    path : Name.t list;
    base : Name.t}
  
  let of_path (p : Path.t) : t =
    let rec aux p =
      match p with
      | Path.Pident i -> { path = []; base = Name.of_ident i }
      | Path.Pdot (p, s, _) ->
        let i = aux p in
        { path = s :: i.path; base = i.base }
      | Path.Papply _ -> failwith "application of paths not handled" in
    let p = aux p in
    (* We convert identifiers from OCaml to their Coq's equivalents *)
    match p with
    | { path = []; base = "()" } -> { path = []; base = "tt" }
    | { path = []; base = "int" } -> { path = []; base = "nat" }
    | _ -> p
  
  let pp (f : Format.formatter) (i : t) : unit =
    List.iter (Name.pp f) i.path;
    Name.pp f i.base
end

module Type = struct
  type t =
    | Variable of Name.t
    | Arrow of t * t
    | Tuple of t list
    | Apply of Ident.t * t list
  
  let rec pp (f : Format.formatter) (typ : t) : unit =
    match typ with
    | Variable x -> Name.pp f x
    | Arrow (typ_x, typ_y) ->
      Format.fprintf f "(";
      pp f typ_x;
      Format.fprintf f "@ ->@ ";
      pp f typ_y;
      Format.fprintf f ")"
    | Tuple typs ->
      (match typs with
      | [] -> Format.fprintf f "unit"
      | typ :: typss ->
        Format.fprintf f "(";
        pp f typ;
        List.iter (fun typ -> Format.fprintf f "@ *@ "; pp f typ) (List.tl typs);
        Format.fprintf f ")")
    | Apply (constr, typs) ->
      Format.fprintf f "(";
      Ident.pp f constr;
      List.iter (fun typ -> Format.fprintf f "@ "; pp f typ) typs;
      Format.fprintf f ")"
end

module Schema = struct
  type t = {
    variables : Name.t list;
    typ : Type.t}
  
  let of_type_expr (typ : Types.type_expr) : t =
    let rec aux typ : Name.Set.t * Type.t =
      match typ.Types.desc with
      | Types.Tvar None ->
        let x = Printf.sprintf "A%d" typ.Types.id in
        (Name.Set.singleton x, Type.Variable x)
      | Types.Tarrow (_, typ_x, typ_y, _) ->
        let (s_x, typ_x) = aux typ_x in
        let (s_y, typ_y) = aux typ_y in
        (Name.Set.union s_x s_y, Type.Arrow (typ_x, typ_y))
      | Types.Ttuple typs ->
        let (ss, typs) = List.split (List.map aux typs) in
        (List.fold_left Name.Set.union Name.Set.empty ss, Type.Tuple typs)
      | Types.Tconstr (path, typs, _) ->
        let (ss, typs) = List.split (List.map aux typs) in
        (List.fold_left Name.Set.union Name.Set.empty ss, Type.Apply (Ident.of_path path, typs))
      | Types.Tlink typ -> aux typ
      | _ -> failwith "type not handled" in
    let (s, typ) = aux typ in
    { variables = Name.Set.elements s; typ = typ }
  
  let of_expression (e : Typedtree.expression) : t =
    of_type_expr e.Typedtree.exp_type
  
  let pp (f : Format.formatter) (schema : t) : unit =
    (match schema.variables with
    | [] -> ()
    | xs ->
      Format.fprintf f "forall@ (";
      List.iter (fun x -> Name.pp f x; Format.fprintf f "@ ") xs;
      Format.fprintf f ":@ Type),@ ");
    Type.pp f schema.typ
end

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
    | String s -> Format.fprintf f "\"%s\" %% string" s
end

module Exp = struct
  type t =
    | Constant of Constant.t
    | Variable of Ident.t
    | Tuple of t list
    | Constructor of Ident.t * t list
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
    | Texp_apply (e_f, e_xs) ->
      let e_f = of_expression e_f in
      let e_xs = List.map (fun (_, e_x, _) ->
        match e_x with
        | Some e_x -> of_expression e_x
        | None -> failwith "expected an argument") e_xs in
      Apply (e_f, e_xs)
    | Texp_tuple es -> Tuple (List.map of_expression es)
    | Texp_construct (path, _, _, es, _) -> Constructor (Ident.of_path path, List.map of_expression es)
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
    | Constructor (x, es) ->
      open_paren ();
      Ident.pp f x;
      List.iter (fun e -> Format.fprintf f "@ "; pp f true e) es;
      close_paren ()
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

module Definition = struct
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
  let (structure, signature) = parse file_name in
  let definitions = Definitions.of_structure structure in
  (*let err = Format.err_formatter in
  Printtyped.implementation err structure;
  Printtyp.signature err signature;*)
  let std = Format.std_formatter in
  Format.fprintf std "Require Import String.@\n\n";
  Definitions.pp std definitions

let main () =
  Arg.parse [] parse_and_print "Usage: ..." (* FIXME: usage *)

;;main ()
