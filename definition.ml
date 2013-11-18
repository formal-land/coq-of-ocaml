open Typedtree

module Value = struct
  type t = {
    name : Name.t;
    free_type_vars : Name.t list;
    args : (Name.t * Type.t) list;
    body : Exp.t * Type.t;
    is_rec : Recursivity.t}
  
  let pp (f : Format.formatter) (value : t) : unit =
    (match value.is_rec with
      | Recursivity.Recursive -> Format.fprintf f "Fixpoint@ "
      | Recursivity.NonRecursive -> Format.fprintf f "Definition@ ");
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
    free_type_vars : Name.t list;
    constructors : (Name.t * Type.t list) list}
  
  let pp (f : Format.formatter) (ind : t) : unit =
    Format.fprintf f "Inductive@ ";
    Name.pp f ind.name;
    if ind.free_type_vars <> [] then (
      Format.fprintf f "@ (";
      Pp.sep_by ind.free_type_vars (fun _ -> Format.fprintf f "@ ") (Name.pp f);
      Format.fprintf f "@ :@ Type)");
    Format.fprintf f "@ :@ Type@ :=@\n";
    Pp.sep_by ind.constructors (fun _ -> Format.fprintf f "@\n") (fun (constr, args) ->
      Format.fprintf f "|@ ";
      Name.pp f constr;
      Format.fprintf f "@ :@ ";
      List.iter (fun arg -> Type.pp f true arg; Format.fprintf f "@ ->@ ") args;
      Name.pp f ind.name;
      List.iter (fun x -> Format.fprintf f "@ "; Name.pp f x) ind.free_type_vars);
    Format.fprintf f ".@\n";
    Pp.sep_by ind.constructors (fun _ -> Format.fprintf f "@\n") (fun (name, args) ->
      Format.fprintf f "Arguments@ ";
      Name.pp f name;
      List.iter (fun x ->
        Format.fprintf f "@ {";
        Name.pp f x;
        Format.fprintf f "}")
        ind.free_type_vars;
      List.iter (fun _ -> Format.fprintf f "@ _") args;
      Format.fprintf f ".")
end

module Record = struct
  type t = {
    name : Name.t;
    fields : (Name.t * Type.t) list }

  let pp (f : Format.formatter) (r : t) : unit =
    Format.fprintf f "Record@ ";
    Name.pp f r.name;
    Format.fprintf f "@ :=@ {@\n";
    Pp.sep_by r.fields (fun _ -> Format.fprintf f ";@\n") (fun (x, typ) ->
      Name.pp f x;
      Format.fprintf f "@ :@ ";
      Type.pp f false typ);
    Format.fprintf f "@ }."
end

module Open = struct
  type t = PathName.t

  let pp (f : Format.formatter) (o : t): unit =
    Format.fprintf f "Require Import@ ";
    PathName.pp f o;
    Format.fprintf f "."
end

type t =
  | Value of Value.t
  | Inductive of Inductive.t
  | Record of Record.t
  | Open of Open.t
  | Module of Name.t * t list

let rec of_structure (structure : structure) : t list =
  let of_structure_item (item : structure_item) : t =
    match item.str_desc with
    | Tstr_value (rec_flag, [{pat_desc = Tpat_var (name, _)}, e]) ->
      let name = Name.of_ident name in
      let schema = Schema.of_type (Type.of_type_expr e.exp_type) in
      let free_type_vars = schema.Schema.variables in
      let (arg_names, body_exp) = Exp.open_function (Exp.of_expression e) in
      let (arg_typs, body_typ) = Type.open_function schema.Schema.typ (List.length arg_names) in
      Value {
        Value.name = name;
        free_type_vars = free_type_vars;
        args = List.combine arg_names arg_typs;
        body = (body_exp, body_typ);
        is_rec = Recursivity.of_rec_flag rec_flag }
    | Tstr_type [name, _, typ] ->
      (match typ.typ_kind with
      | Ttype_variant cases ->
        let constructors = List.map (fun (constr, _, typs, _) ->
          (Name.of_ident constr, List.map (fun typ -> Type.of_type_expr typ.ctyp_type) typs))
          cases in
        let free_type_vars = List.map (fun name ->
          match name with
          | Some x -> x.Asttypes.txt
          | None -> failwith "Type parameter expected.")
          typ.typ_params in
        Inductive {
          Inductive.name = Name.of_ident name;
          free_type_vars = free_type_vars;
          constructors = constructors }
      | Ttype_record fields ->
        Record {
          Record.name = Name.of_ident name;
          fields = List.map (fun (x, _, _, typ, _) -> (Name.of_ident x, Type.of_type_expr typ.ctyp_type)) fields }
      | _ -> failwith "Type definition not handled.")
    | Tstr_open (path, _) -> Open (PathName.of_path path)
    | Tstr_module (name, _, { mod_desc = Tmod_structure structure }) ->
      Module (Name.of_ident name, of_structure structure)
    | Tstr_exception _ -> failwith "Imperative structure item not handled."
    | _ -> failwith "Structure item not handled." in
  List.map of_structure_item structure.str_items

let rec pp (f : Format.formatter) (defs : t list) : unit =
  let pp_one (def : t) : unit =
    match def with
    | Value value -> Value.pp f value
    | Inductive ind -> Inductive.pp f ind
    | Record record -> Record.pp f record
    | Open o -> Open.pp f o
    | Module (name, defs) ->
      Format.fprintf f "Module@ ";
      Name.pp f name;
      Format.fprintf f ".@\n";
      pp f defs;
      Format.fprintf f "@\nEnd@ ";
      Name.pp f name;
      Format.fprintf f "." in
  Pp.sep_by defs (fun _ -> Format.fprintf f "@\n@\n") (fun def -> pp_one def)