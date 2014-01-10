(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open Types
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type t = {
    name : Name.t;
    free_typ_vars : Name.t list; (** Polymorphic type variables. *)
    args : (Name.t * Type.t) list; (** Names and types of the arguments. *)
    body : Exp.t * Type.t; (** Body and type of the body. *)
    is_rec : Recursivity.t (** If the function is recursive. *) }
  
  (** Pretty-print a value definition. *)
  let pp (value : t) : SmartPrint.t =
    nest (
      (if Recursivity.to_bool value.is_rec then
        !^ "Fixpoint"
      else
        !^ "Definition") ^^
      Name.pp value.name ^^
      (match value.free_typ_vars with
      | [] -> empty
      | xs -> braces @@ group (separate space (List.map Name.pp xs) ^^ !^ ":" ^^ !^ "Type")) ^^
      group (separate space (value.args |> List.map (fun (x, t) ->
        parens @@ nest (Name.pp x ^^ !^ ":" ^^ Type.pp false t)))) ^^
      !^ ":" ^^ Type.pp false (snd value.body) ^^
      !^ ":=" ^^ Exp.pp false (fst value.body) ^-^ !^ ".")
end

(** A definition of a sum type. *)
module Inductive = struct
  type t = {
    name : Name.t;
    free_typ_vars : Name.t list; (** Polymorphic type variables. *)
    constructors : (Name.t * Type.t list) list
      (** The list of constructors, each with a name and the list of the types of the arguments. *) }
  
  (** Pretty-print a sum type definition. *)
  let pp (ind : t) : SmartPrint.t =
    nest (
      !^ "Inductive" ^^ Name.pp ind.name ^^
      (if ind.free_typ_vars = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.pp ind.free_typ_vars) ^^
        !^ ":" ^^ !^ "Type")) ^^
      !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^^ newline ^^
      separate newline (ind.constructors |> List.map (fun (constr, args) ->
        nest (
          !^ "|" ^^ Name.pp constr ^^ !^ ":" ^^
          separate space (args |> List.map (fun arg -> Type.pp true arg ^^ !^ "->")) ^^ Name.pp ind.name ^^
          separate space (List.map Name.pp ind.free_typ_vars)))) ^-^ !^ "." ^^ newline ^^
      separate newline (ind.constructors |> List.map (fun (name, args) ->
        nest (
          !^ "Arguments" ^^ Name.pp name ^^
          separate space (ind.free_typ_vars |> List.map (fun x -> braces @@ Name.pp x)) ^^
          separate space (List.map (fun _ -> !^ "_") args) ^-^ !^ "."))))
end

(** A definition of a record. *)
module Record = struct
  type t = {
    name : Name.t;
    fields : (Name.t * Type.t) list (** The names of the fields with their types. *) }

  (** Pretty-print a record definition. *)
  let pp (r : t) : SmartPrint.t =
    nest (
      !^ "Record" ^^ Name.pp r.name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (r.fields |> List.map (fun (x, typ) ->
        nest (Name.pp x ^^ !^ ":" ^^ Type.pp false typ)))) ^^
      !^ "}.")
end

(** The "open" construct to open a module. *)
module Open = struct
  type t = PathName.t

  (** Pretty-print an open construct. *)
  let pp (o : t): SmartPrint.t =
    nest (!^ "Require Import" ^^ PathName.pp o ^-^ !^ ".")
end

(** A structure. *)
type t =
  | Value of Value.t
  | Inductive of Inductive.t
  | Record of Record.t
  | Open of Open.t
  | Module of Name.t * t list

(** Import an OCaml structure. *)
let rec of_structure (structure : structure)
  (path : PathName.Path.t) (effects : Effect.Env.t)
  : t list * Effect.Env.t =
  let of_structure_item (item : structure_item)
    (path : PathName.Path.t) (effects : Effect.Env.t)
    : t * Effect.Env.t =
    match item.str_desc with
    | Tstr_value (is_rec, [{vb_pat = {pat_desc = Tpat_var (name, _)}; vb_expr = e}]) ->
      let (is_rec, name, free_typ_vars, args, e_typ, e) =
        Exp.import_let_fun is_rec name e in
      let name_typ = Effect.function_typ args
        { Effect.effect = false; typ = Effect.Type.of_type e_typ } in
      let effects_in_e =
        if Recursivity.to_bool is_rec then
          PathName.Map.add (PathName.of_name path name) name_typ effects
        else
          effects in
      let effects_in_e = Effect.Env.in_function path effects_in_e args in
      let (e, e_effect) = Exp.monadise e path effects_in_e in
      if e_effect.Effect.effect && args = [] then
        failwith "Cannot have effects at toplevel.";
      let e_exp = Exp.simplify e in
      let effect_typ = Effect.function_typ args e_effect in
      let effects = PathName.Map.add (PathName.of_name path name) effect_typ effects in
      (Value {
        Value.name = name;
        free_typ_vars = free_typ_vars;
        args = args;
        body = (e_exp, e_typ);
        is_rec = is_rec },
        effects)
    | Tstr_type [{typ_id = name; typ_type = typ}] ->
      (match typ.type_kind with
      | Type_variant cases ->
        let constructors = List.map (fun {cd_id = constr; cd_args = typs} ->
          (Name.of_ident constr, List.map (fun typ -> Type.of_type_expr typ) typs))
          cases in
        let free_typ_vars = List.map (fun x ->
          match Type.of_type_expr x with
          | Type.Variable x -> x
          | _ -> failwith "The type parameter was expected to be a variable.")
          typ.type_params in
        (Inductive {
          Inductive.name = Name.of_ident name;
          free_typ_vars = free_typ_vars;
          constructors = constructors },
          effects)
      | Type_record (fields, _) ->
        (Record {
          Record.name = Name.of_ident name;
          fields = List.map (fun {ld_id = x; ld_type = typ} -> (Name.of_ident x, Type.of_type_expr typ)) fields },
          effects)
      | _ -> failwith "Type definition not handled.")
    | Tstr_open (_, path, _, _) -> (Open (PathName.of_path path), effects)
    | Tstr_module {mb_id = name; mb_expr = { mod_desc = Tmod_structure structure }} ->
      let name = Name.of_ident name in
      let (structures, effects) = of_structure structure (name :: path) effects in
      (Module (name, structures), effects)
    | Tstr_exception _ -> failwith "Imperative structure item not handled."
    | _ -> failwith "Structure item not handled." in
  let (structures, effects) =
    List.fold_left (fun (structures, effects) item ->
      let (structure, effects) = of_structure_item item path effects in
      (structure :: structures, effects))
      ([], effects) structure.str_items in
  (List.rev structures, effects)

(*let rec signature (def : t) : Signature.t option =
  let rec remove_nones (l : 'a option list) : 'a list =
    match l with
    | [] -> []
    | None :: xs -> remove_nones xs
    | Some x :: xs -> x :: remove_nones xs in
  match def with
  | Value { Value.name = name } -> Some (Signature.Value (name, false))
  | Inductive _ | Record _ | Open _ -> None
  | Module (name, defs) ->
    Some (Signature.Module (name,
      defs |> List.map signature |> remove_nones))*)

(** Pretty-print a structure. *)
let rec pp (defs : t list) : SmartPrint.t =
  let pp_one (def : t) : SmartPrint.t =
    match def with
    | Value value -> Value.pp value
    | Inductive ind -> Inductive.pp ind
    | Record record -> Record.pp record
    | Open o -> Open.pp o
    | Module (name, defs) ->
      nest (
        !^ "Module" ^^ Name.pp name ^-^ !^ "." ^^ newline ^^
        indent (pp defs) ^^ newline ^^
        !^ "End" ^^ Name.pp name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map pp_one defs)