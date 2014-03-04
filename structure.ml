(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open Types
open SmartPrint
open Common

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type 'a t = {
    header : Exp.Header.t;
    body : 'a Exp.t (** Body expression. *) }

  let pp (pp_a : 'a -> SmartPrint.t) (value : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ Exp.Header.pp value.header ^^ !^ "=" ^^ newline ^^
      indent (Exp.pp pp_a value.body))
  
  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : 'a t) : SmartPrint.t =
    let (is_rec, x, typ_vars, args, typ) = value.header in
    nest (
      (if Recursivity.to_bool is_rec then
        !^ "Fixpoint"
      else
        !^ "Definition") ^^
      Name.to_coq x ^^
      (match typ_vars with
      | [] -> empty
      | _ :: _ ->
        braces @@ group (separate space (List.map Name.to_coq typ_vars) ^^
        !^ ":" ^^ !^ "Type")) ^^
      group (separate space (args |> List.map (fun (x, t) ->
        parens @@ nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false t)))) ^^
      (match typ with
      | None -> empty
      | Some typ -> !^ ":" ^^ Type.to_coq false typ) ^^
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
    nest (!^ "Inductive" ^^ Name.pp ind.name ^-^ !^ ":" ^^ newline ^^ indent (OCaml.tuple [
      OCaml.list Name.pp ind.typ_vars;
      OCaml.list (fun (x, typs) -> OCaml.tuple [Name.pp x; OCaml.list Type.pp typs]) ind.constructors]))

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
    nest (!^ "Record" ^^ Name.pp r.name ^-^ !^ ":" ^^ newline ^^ indent (OCaml.tuple [
      OCaml.list (fun (x, typ) -> OCaml.tuple [Name.pp x; Type.pp typ]) r.fields]))

  (** Pretty-print a record definition to Coq. *)
  let to_coq (r : t) : SmartPrint.t =
    nest (
      !^ "Record" ^^ Name.to_coq r.name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (r.fields |> List.map (fun (x, typ) ->
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}.")
end

(** Definition of a synonym type. *)
module Synonym = struct
  type t = {
    name : Name.t;
    typ_vars : Name.t list;
    value : Type.t }

  let pp (s : t) : SmartPrint.t =
    nest (!^ "Synonym" ^^ OCaml.tuple [
      Name.pp s.name; OCaml.list Name.pp s.typ_vars; Type.pp s.value])

  let to_coq (s : t) : SmartPrint.t =
    nest (
      !^ "Definition" ^^ Name.to_coq s.name ^^
      separate space (List.map Name.to_coq s.typ_vars) ^^ !^ ":=" ^^
      Type.to_coq false s.value ^-^ !^ ".")
end

module Exception = struct
  type t = {
    name : Name.t;
    typ : Type.t }

  let pp (exn : t) : SmartPrint.t =
    nest (!^ "Exception" ^^ OCaml.tuple [Name.pp exn.name; Type.pp exn.typ])

  let effect_name (exn : t) : string =
    "Err_" ^ exn.name

  let atom (exn : t) : Effect.Atom.t = {
    Effect.Atom.name = exn.name;
    kind = Effect.Atom.Kind.Error;
    coq_type = Type.to_coq false exn.typ }

  let raise_effect_typ (exn : t) : Effect.Type.t =
    Effect.Type.Arrow (Effect.Descriptor.of_atom (atom exn), Effect.Type.Pure)

  let to_coq (exn : t) : SmartPrint.t =
    !^ "Definition" ^^ Name.to_coq (effect_name exn) ^^ !^ ":=" ^^
    !^ "Effect.new" ^^ !^ "unit" ^^ Type.to_coq true exn.typ ^-^ !^ "." ^^
    newline ^^ newline ^^
    !^ "Definition" ^^ Name.to_coq exn.name ^^ !^ "{A : Type}" ^^
    nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false exn.typ)) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ !^ (effect_name exn) ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
    newline ^^ indent (
      !^ "fun s => (inr (inl x), s).")
end

(*module Reference = struct
  type t = {
    name : Name.t;
    typ : Type.t }

  let pp (r : t) : SmartPrint.t =
    nest (!^ "Reference" ^^ OCaml.tuple [Name.pp r.name; Type.pp r.typ])

  let effect_name (r : t) : string =
    "Ref_" ^ r.name

  let atom (r : t) : Effect.Atom.t = {
    Effect.Atom.name = r.name;
    kind = Effect.Atom.Kind.State;
    coq_type = Type.to_coq false r.typ }

  let read_write_effect_typ (r : t) : Effect.Type.t =
    Effect.Type.Arrow (Effect.Descriptor.of_atom (atom r), Effect.Type.Pure)

  let to_coq (r : t) : SmartPrint.t =
    !^ "Definition" ^^ Name.to_coq (effect_name r) ^^ !^ ":=" ^^
    !^ "Effect.new" ^^ Type.to_coq true r.typ ^^ !^ "unit" ^-^ !^ "." ^^
    newline ^^ newline ^^
    !^ "Definition" ^^ Name.to_coq (r.name) ^^ !^ "{A : Type}" ^^
    nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false r.typ)) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ !^ (effect_name r) ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
    newline ^^ indent (
      !^ "fun s => (inr (inl x), s).")
end*)

(** The "open" construct to open a module. *)
module Open = struct
  type t = PathName.t

  let pp (o : t) : SmartPrint.t =
    nest (!^ "Open" ^^ OCaml.tuple [PathName.pp o])

  (** Pretty-print an open construct to Coq. *)
  let to_coq (o : t): SmartPrint.t =
    nest (!^ "Require Import" ^^ PathName.to_coq o ^-^ !^ ".")
end

(** A structure. *)
type ('a, 'b) t =
  | Value of 'a * 'b Value.t
  | Inductive of Inductive.t
  | Record of Record.t
  | Synonym of Synonym.t
  | Exception of Exception.t
  | Open of Open.t
  | Module of Name.t * ('a, 'b) t list

let rec pp (pp_a : 'a -> SmartPrint.t) (pp_b : 'b -> SmartPrint.t)
  (defs : ('a, 'b) t list) : SmartPrint.t =
  let pp_one (def : ('a, 'b) t) : SmartPrint.t =
    match def with
    | Value (a, value) -> OCaml.tuple [pp_a a; Value.pp pp_b value]
    | Inductive ind -> Inductive.pp ind
    | Record record -> Record.pp record
    | Synonym synonym -> Synonym.pp synonym
    | Exception exn -> Exception.pp exn
    | Open o -> Open.pp o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
        indent (pp pp_a pp_b defs)) in
  separate (newline ^^ newline) (List.map pp_one defs)

(** Import an OCaml structure. *)
let rec of_structure (structure : structure) : (unit, Loc.t) t list =
  let of_structure_item (item : structure_item) : (unit, Loc.t) t =
    match item.str_desc with
    | Tstr_value (is_rec, [{vb_pat = pattern; vb_expr = e}]) ->
      let (is_rec, pattern, typ_vars, args, typ, e) =
        Exp.import_let_fun is_rec pattern e in
      (match pattern with
      | Pattern.Variable x ->
        Value ((), {
          Value.header = (is_rec, x, typ_vars, args, Some typ);
          body = e })
      | _ -> failwith "Cannot match a function definition on a pattern.")
    | Tstr_type [{typ_id = name; typ_type = typ}] ->
      let typ_vars = typ.type_params |> List.map (fun x ->
        match Type.of_type_expr x with
        | Type.Variable x -> x
        | _ -> failwith "The type parameter was expected to be a variable.") in
      (match typ.type_kind with
      | Type_variant cases ->
        let constructors = List.map (fun {cd_id = constr; cd_args = typs} ->
          (Name.of_ident constr, List.map (fun typ -> Type.of_type_expr typ) typs))
          cases in
        Inductive {
          Inductive.name = Name.of_ident name;
          typ_vars = typ_vars;
          constructors = constructors }
      | Type_record (fields, _) ->
        Record {
          Record.name = Name.of_ident name;
          fields = fields |> List.map (fun {ld_id = x; ld_type = typ} ->
            (Name.of_ident x, Type.of_type_expr typ)) }
      | Type_abstract ->
        (match typ.type_manifest with
        | Some typ ->
          Synonym {
            Synonym.name = Name.of_ident name;
            typ_vars = typ_vars;
            value = Type.of_type_expr typ }
        | None -> failwith "Type definition not handled."))
    | Tstr_exception { cd_id = name; cd_args = args } ->
      let typ =
        Type.Tuple (args |> List.map (fun { ctyp_type = typ } ->
          Type.of_type_expr typ)) in
      Exception { Exception.name = Name.of_ident name; typ = typ}
    | Tstr_open (_, path, _, _) -> Open (PathName.of_path path)
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc = Tmod_structure structure }} ->
      let name = Name.of_ident name in
      let structures = of_structure structure in
      Module (name, structures)
    | _ -> failwith "Structure item not handled." in
  List.map of_structure_item structure.str_items

let rec monadise_let_rec (defs : (unit, Loc.t) t list) : (unit, Loc.t) t list =
  let rec monadise_let_rec_one (def : (unit, Loc.t) t) : (unit, Loc.t) t list =
    match def with
    | Value ((), { Value.header = header; body = body }) ->
      let defs = Exp.monadise_let_rec_definition header body in
      defs |> List.map (fun (header, body) ->
        Value ((), { Value.header = header; body = body }))
    | Module (name, defs) -> [Module (name, monadise_let_rec defs)]
    | Inductive _ | Record _ | Synonym _ | Exception _ | Open _ -> [def] in
  List.concat (List.map monadise_let_rec_one defs)

let rec effects (env_atoms : env_atoms) (env_effects : env_effects)
  (defs : (unit, 'a) t list)
  : env_atoms * env_effects * (Effect.Type.t, 'a * Effect.t) t list =
  let rec effects_one (env_atoms : env_atoms) (env_effects : env_effects)
    (def : (unit, 'a) t)
    : env_atoms * env_effects * (Effect.Type.t, 'a * Effect.t) t =
    match def with
    | Value ((), {
      Value.header = (is_rec, x, _, args, _) as header;
      body = e }) ->
      let (e, x_typ) = Exp.effects_of_let env_effects is_rec x args e in
      let env_effects = PathName.Env.add_name x x_typ env_effects in
      (env_atoms, env_effects,
        Value (x_typ, { Value.header = header; body = e }))
    | Module (name, defs) ->
      let (env_atoms, env_effects, defs) =
        effects (PathName.Env.open_module env_atoms)
          (PathName.Env.open_module env_effects) defs in
      (PathName.Env.close_module env_atoms name,
        PathName.Env.close_module env_effects name, Module (name, defs))
    | Exception exn ->
      let env_effects = PathName.Env.add_name exn.Exception.name
        (Exception.raise_effect_typ exn) env_effects in
      (env_atoms, env_effects, Exception exn)
    | Inductive ind -> (env_atoms, env_effects, Inductive ind)
    | Record record -> (env_atoms, env_effects, Record record)
    | Synonym synonym -> (env_atoms, env_effects, Synonym synonym)
    | Open name -> (env_atoms, env_effects, Open name) in
  let (env_atoms, env_effects, defs) =
    List.fold_left (fun (env_atoms, env_effects, defs) def ->
      let (env_atoms, env_effects, def) =
        effects_one env_atoms env_effects def in
      (env_atoms, env_effects, def :: defs))
      (env_atoms, env_effects, []) defs in
  (env_atoms, env_effects, List.rev defs)

let rec monadise (env : unit PathName.Env.t)
  (defs : (Effect.Type.t, Loc.t * Effect.t) t list)
  : unit PathName.Env.t * (unit, Loc.t) t list =
  let rec monadise_one (env : unit PathName.Env.t)
    (def : (Effect.Type.t, Loc.t * Effect.t) t)
    : unit PathName.Env.t * (unit, Loc.t) t =
    match def with
    | Value (effect, {
      Value.header = (is_rec, x, typ_vars, args, typ);
      body = body }) ->
      let typ = match typ with
        | None -> None
        | Some typ -> Some (Type.monadise typ (snd (Exp.annotation body))) in
      let env_in_body =
        if Recursivity.to_bool is_rec then
          PathName.Env.add_name x () env
        else
          env in
      let body = Exp.monadise env_in_body body in
      let env = PathName.Env.add_name x () env in
      (env, Value ((), {
        Value.header = (is_rec, x, typ_vars, args, typ);
        body = body }))
    | Module (name, defs) ->
      let (env, defs) = monadise (PathName.Env.open_module env) defs in
      (PathName.Env.close_module env name, Module (name, defs))
    | Exception exn ->
      (PathName.Env.add_name exn.Exception.name () env, Exception exn)
    | Inductive ind -> (env, Inductive ind)
    | Record record -> (env, Record record)
    | Synonym synonym -> (env, Synonym synonym)
    | Open name -> (env, Open name) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env, def) = monadise_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : ('a, 'b) t list) : SmartPrint.t =
  let to_coq_one (def : ('a, 'b) t) : SmartPrint.t =
    match def with
    | Value (_, value) -> Value.to_coq value
    | Inductive ind -> Inductive.to_coq ind
    | Record record -> Record.to_coq record
    | Synonym s -> Synonym.to_coq s
    | Exception exn -> Exception.to_coq exn
    | Open o -> Open.to_coq o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)