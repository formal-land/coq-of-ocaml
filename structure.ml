(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open Types
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = {
    name : Name.t;
    is_rec : Recursivity.t; (** If the function is recursive. *)
    typ_vars : Name.t list; (** Polymorphic type variables. *)
    args : (Name.t * Type.t) list; (** Names and types of the arguments. *)
    typ : Type.t; (** Type of the body. *)
    body : Exp.t (** Body expression. *) }

  let pp (value : t) : SmartPrint.t =
    nest (!^ "Value" ^^ Name.pp value.name ^-^ !^ ":" ^^ newline ^^ indent (Pp.list [
      Recursivity.pp value.is_rec;
      OCaml.list Name.pp value.typ_vars;
      OCaml.list (fun (x, typ) -> Pp.list [Name.pp x; Type.pp typ]) value.args;
      Type.pp value.typ; Exp.pp value.body]))
  
  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : t) : SmartPrint.t =
    nest (
      (if Recursivity.to_bool value.is_rec then
        !^ "Fixpoint"
      else
        !^ "Definition") ^^
      Name.to_coq value.name ^^
      (match value.typ_vars with
      | [] -> empty
      | xs -> braces @@ group (separate space (List.map Name.to_coq xs) ^^ !^ ":" ^^ !^ "Type")) ^^
      group (separate space (value.args |> List.map (fun (x, t) ->
        parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false t)))) ^^
      !^ ":" ^^ Type.to_coq false value.typ ^^
      !^ ":=" ^^ Exp.to_coq false value.body ^-^ !^ ".")
end

(** A definition of a sum type. *)
module Inductive = struct
  type t = {
    name : Name.t;
    typ_vars : Name.t list; (** Polymorphic type variables. *)
    constructors : (Name.t * Type.t list) list
      (** The list of constructors, each with a name and the list of the types of the arguments. *) }
  
  let pp (ind : t) : SmartPrint.t =
    nest (!^ "Inductive" ^^ Name.pp ind.name ^-^ !^ ":" ^^ newline ^^ indent (Pp.list [
      OCaml.list Name.pp ind.typ_vars;
      OCaml.list (fun (x, typs) -> Pp.list [Name.pp x; OCaml.list Type.pp typs]) ind.constructors]))

  (** Pretty-print a sum type definition to Coq. *)
  let to_coq (ind : t) : SmartPrint.t =
    nest (
      !^ "Inductive" ^^ Name.to_coq ind.name ^^
      (if ind.typ_vars = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.to_coq ind.typ_vars) ^^
        !^ ":" ^^ !^ "Type")) ^^
      !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^^ newline ^^
      separate newline (ind.constructors |> List.map (fun (constr, args) ->
        nest (
          !^ "|" ^^ Name.to_coq constr ^^ !^ ":" ^^
          separate space (args |> List.map (fun arg -> Type.to_coq true arg ^^ !^ "->")) ^^ Name.to_coq ind.name ^^
          separate space (List.map Name.to_coq ind.typ_vars)))) ^-^ !^ "." ^^ newline ^^
      separate newline (ind.constructors |> List.map (fun (name, args) ->
        nest (
          !^ "Arguments" ^^ Name.to_coq name ^^
          separate space (ind.typ_vars |> List.map (fun x -> braces @@ Name.to_coq x)) ^^
          separate space (List.map (fun _ -> !^ "_") args) ^-^ !^ "."))))
end

(** A definition of a record. *)
module Record = struct
  type t = {
    name : Name.t;
    fields : (Name.t * Type.t) list (** The names of the fields with their types. *) }

  let pp (r : t) : SmartPrint.t =
    nest (!^ "Record" ^^ Name.pp r.name ^-^ !^ ":" ^^ newline ^^ indent (Pp.list [
      OCaml.list (fun (x, typ) -> Pp.list [Name.pp x; Type.pp typ]) r.fields]))

  (** Pretty-print a record definition to Coq. *)
  let to_coq (r : t) : SmartPrint.t =
    nest (
      !^ "Record" ^^ Name.to_coq r.name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (r.fields |> List.map (fun (x, typ) ->
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}.")
end

(** The "open" construct to open a module. *)
module Open = struct
  type t = PathName.t

  let pp (o : t) : SmartPrint.t =
    nest (!^ "Open" ^^ Pp.list [PathName.pp o])

  (** Pretty-print an open construct to Coq. *)
  let to_coq (o : t): SmartPrint.t =
    nest (!^ "Require Import" ^^ PathName.to_coq o ^-^ !^ ".")
end

(** A structure. *)
type t =
  | Value of Value.t
  | Inductive of Inductive.t
  | Record of Record.t
  | Open of Open.t
  | Module of Name.t * t list

let rec pp (defs : t list) : SmartPrint.t =
  let pp_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.pp value
    | Inductive ind -> Inductive.pp ind
    | Record record -> Record.pp record
    | Open o -> Open.pp o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
        indent (pp defs)) in
  separate (newline ^^ newline) (List.map pp_one defs)

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : t list =
  let of_structure_item (item : structure_item) : t =
    match item.str_desc with
    | Tstr_value (is_rec, [{vb_pat = pattern; vb_expr = e}]) ->
      let (is_rec, pattern, typ_vars, args, e_typ, e) =
        Exp.import_let_fun is_rec pattern e in
      (match pattern with
      | Pattern.Variable name ->
        Value {
          Value.name = name;
          is_rec = is_rec;
          typ_vars = typ_vars;
          args = args;
          typ = e_typ;
          body = e }
      | _ -> failwith "Cannot match a function definition on a pattern.")
    | Tstr_type [{typ_id = name; typ_type = typ}] ->
      (match typ.type_kind with
      | Type_variant cases ->
        let constructors = List.map (fun {cd_id = constr; cd_args = typs} ->
          (Name.of_ident constr, List.map (fun typ -> Type.of_type_expr typ) typs))
          cases in
        let typ_vars = List.map (fun x ->
          match Type.of_type_expr x with
          | Type.Variable x -> x
          | _ -> failwith "The type parameter was expected to be a variable.")
          typ.type_params in
        Inductive {
          Inductive.name = Name.of_ident name;
          typ_vars = typ_vars;
          constructors = constructors }
      | Type_record (fields, _) ->
        Record {
          Record.name = Name.of_ident name;
          fields = List.map (fun {ld_id = x; ld_type = typ} -> (Name.of_ident x, Type.of_type_expr typ)) fields }
      | _ -> failwith "Type definition not handled.")
    | Tstr_open (_, path, _, _) -> Open (PathName.of_path path)
    | Tstr_module {mb_id = name; mb_expr = { mod_desc = Tmod_structure structure }} ->
      let name = Name.of_ident name in
      let structures = of_structure structure in
      Module (name, structures)
    | Tstr_exception _ -> failwith "Imperative structure item not handled."
    | _ -> failwith "Structure item not handled." in
  List.map of_structure_item structure.str_items

module Tree = struct
  type t =
    | Value of Exp.Tree.t * Effect.Type.t
    | Module of t list
    | Other

  let rec pps (trees : t list) : SmartPrint.t =
    let pp (tree : t) : SmartPrint.t =
      match tree with
      | Value (tree, typ) -> nest (!^ "Value" ^^ Pp.list [
        Effect.Type.pp false typ; Exp.Tree.pp tree])
      | Module trees ->
        nest (
          !^ "Module" ^^ newline ^^
          indent (pps trees))
      | Other -> !^ "Other" in
    separate (newline ^^ newline) (List.map pp trees)
end

let rec to_trees (effects : Effect.Env.t)
  (defs : t list) : Tree.t list * Effect.Env.t =
  let rec to_tree (def : t) (effects : Effect.Env.t) : Tree.t * Effect.Env.t =
    match def with
    | Value {
      Value.name = x;
      is_rec = is_rec;
      args = args;
      body = e } ->
      let (tree, x_typ) = Exp.to_tree_let_fun effects is_rec x args e in
      let effects = Effect.Env.add (PathName.of_name [] x) x_typ effects in
      (Tree.Value (tree, x_typ), effects)
    | Module (name, defs) ->
      let (trees, effects) = to_trees (Effect.Env.open_module effects) defs in
      (Tree.Module trees, Effect.Env.close_module effects name)
    | Inductive _ | Record _ | Open _ -> (Tree.Other, effects) in
  let (trees, effects) =
    List.fold_left (fun (trees, effects) def ->
      let (tree, effects) = to_tree def effects in
      (tree :: trees, effects))
      ([], effects) defs in
  (List.rev trees, effects)

let rec monadise (env : PathName.Env.t) (defs : t list) (trees : Tree.t list)
  : PathName.Env.t * t list =
  let rec monadise_one (env : PathName.Env.t) (def : t) (tree : Tree.t)
    : PathName.Env.t * t =
    match (def, tree) with
    | (
      Value {
        Value.name = name;
        is_rec = is_rec;
        typ_vars = typ_vars;
        args = args;
        typ = typ;
        body = body },
      Tree.Value (tree, effect)) ->
      let typ = Type.monadise typ (Exp.Tree.effect tree) in
      let env_in_body =
        if Recursivity.to_bool is_rec then
          PathName.Env.add (PathName.of_name [] name) env
        else
          env in
      let body = Exp.monadise env_in_body body tree in
      let env = PathName.Env.add (PathName.of_name [] name) env in
      (env, Value {
        Value.name = name;
        is_rec = is_rec;
        typ_vars = typ_vars;
        args = args;
        typ = typ;
        body = body })
    | (Module (name, defs), Tree.Module trees) ->
      let (env, defs) = monadise (PathName.Env.open_module env) defs trees in
      (PathName.Env.close_module env name, Module (name, defs))
    | (Inductive _, Tree.Other) | (Record _, Tree.Other)
      | (Open _, Tree.Other) -> (env, def)
    | _ -> failwith "Unexpected arguments for 'monadise'." in
  let (env, defs) =
    List.fold_left2 (fun (env, defs) def tree ->
      let (env, def) = monadise_one env def tree in
      (env, def :: defs))
      (env, []) defs trees in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : t list) : SmartPrint.t =
  let to_coq_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.to_coq value
    | Inductive ind -> Inductive.to_coq ind
    | Record record -> Record.to_coq record
    | Open o -> Open.to_coq o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)