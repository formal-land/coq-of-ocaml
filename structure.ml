(** A structure represents the contents of a ".ml" file. *)
open Typedtree
open Types
open SmartPrint

(** A value is a toplevel definition made with a "let". *)
module Value = struct
  type 'a t = {
    header : Exp.Header.t;
    body : 'a Exp.t (** Body expression. *) }

  let pp (pp_a : 'a -> SmartPrint.t) (value : 'a t) : SmartPrint.t =
    nest (!^ "Value" ^^ Exp.Header.pp value.header ^^ !^ "=" ^^ newline ^^
      indent (Exp.pp pp_a value.body))
  
  let update_env (value : 'a t) (v : 'b) (env : 'b FullEnvi.t) : 'b FullEnvi.t =
    let (_, _, x, _, _, _) = value.header in
    { env with FullEnvi.vars = Envi.add_name x v env.FullEnvi.vars }

  (** Pretty-print a value definition to Coq. *)
  let to_coq (value : 'a t) : SmartPrint.t =
    let (is_rec, _, x, typ_vars, args, typ) = value.header in
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

  let update_env (ind : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
    { env with
      FullEnvi.typs = Envi.add_name ind.name () env.FullEnvi.typs;
      constructors =
        List.fold_left (fun constructors (x, _) ->
          Envi.add_name x () constructors)
          env.FullEnvi.constructors ind.constructors }

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

  let update_env (r : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
    { env with
      FullEnvi.typs = Envi.add_name r.name () env.FullEnvi.typs;
      fields =
        List.fold_left (fun fields (x, _) ->
          Envi.add_name x () fields)
          env.FullEnvi.fields r.fields }

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

  let update_env (s : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
    { env with FullEnvi.typs = Envi.add_name s.name () env.FullEnvi.typs }

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

  let update_env (exn : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    { env with
      FullEnvi.vars = Envi.add_name ("raise_" ^ exn.name) () env.FullEnvi.vars;
      descriptors = Envi.add_name exn.name () env.FullEnvi.descriptors }

  let update_env_with_effects (exn : t) (env : Effect.Type.t FullEnvi.t) (loc : Loc.t)
    : Effect.Type.t FullEnvi.t =
    let env = { env with
      FullEnvi.descriptors = Envi.add_name exn.name () env.FullEnvi.descriptors } in
    let effect_typ =
      Effect.Type.Arrow (
        Effect.Descriptor.singleton
          loc
          (Envi.bound_name (PathName.of_name [] exn.name) env.FullEnvi.descriptors),
        Effect.Type.Pure) in
    { env with
      FullEnvi.vars = Envi.add_name ("raise_" ^ exn.name) effect_typ env.FullEnvi.vars }

  let to_coq (exn : t) : SmartPrint.t =
    !^ "Definition" ^^ Name.to_coq exn.name ^^ !^ ":=" ^^
      !^ "Effect.make" ^^ !^ "unit" ^^ Type.to_coq true exn.typ ^-^ !^ "." ^^
    newline ^^ newline ^^
    !^ "Definition" ^^ Name.to_coq ("raise_" ^ exn.name) ^^ !^ "{A : Type}" ^^
      nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false exn.typ)) ^^ !^ ":" ^^
      !^ "M" ^^ !^ "[" ^^ Name.to_coq exn.name ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
    newline ^^ indent (
      !^ "fun s => (inr (inl x), s).")
end

module Reference = struct
  type t = {
    name : Name.t;
    typ : Type.t }

  let pp (r : t) : SmartPrint.t =
    nest (!^ "Reference" ^^ OCaml.tuple [Name.pp r.name; Type.pp r.typ])

  let update_env (r : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
    { env with
      FullEnvi.vars =
        Envi.add_name ("read_" ^ r.name) () (
        Envi.add_name ("write_" ^ r.name) ()
          (env.FullEnvi.vars));
      descriptors = Envi.add_name r.name () env.FullEnvi.descriptors }

  let update_env_with_effects (r : t) (env : Effect.Type.t FullEnvi.t) (loc : Loc.t)
    : Effect.Type.t FullEnvi.t =
    let env = { env with
      FullEnvi.descriptors = Envi.add_name r.name () env.FullEnvi.descriptors } in
    let effect_typ =
      Effect.Type.Arrow (
        Effect.Descriptor.singleton
          loc
          (Envi.bound_name (PathName.of_name [] r.name) env.FullEnvi.descriptors),
        Effect.Type.Pure) in
    { env with
      FullEnvi.vars =
        Envi.add_name ("read_" ^ r.name) effect_typ (
        Envi.add_name ("write_" ^ r.name) effect_typ
          (env.FullEnvi.vars)) }

  let to_coq (r : t) : SmartPrint.t =
    !^ "Definition" ^^ Name.to_coq r.name ^^ !^ ":=" ^^
      !^ "Effect.make" ^^ Type.to_coq true r.typ ^^ !^ "unit" ^-^ !^ "." ^^
    newline ^^ newline ^^
    !^ "Definition" ^^ Name.to_coq ("read_" ^ r.name) ^^ !^ "(_ : unit)" ^^ !^ ":" ^^
      !^ "M" ^^ !^ "[" ^^ Name.to_coq r.name ^^ !^ "]" ^^ Type.to_coq true r.typ ^^ !^ ":=" ^^
    newline ^^ indent (
      !^ "fun s => (inl (fst s), s).") ^^
    newline ^^ newline ^^
    !^ "Definition" ^^ Name.to_coq ("write_" ^ r.name) ^^ parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false r.typ) ^^ !^ ":" ^^
      !^ "M" ^^ !^ "[" ^^ Name.to_coq r.name ^^ !^ "]" ^^ !^ "unit" ^^ !^ ":=" ^^
    newline ^^ indent (
      !^ "fun s => (inl tt, (x, tt)).")
end

(*
(** The "open" construct to open a module. *)
module Open = struct
  type t = PathName.t

  let pp (o : t) : SmartPrint.t =
    nest (!^ "Open" ^^ OCaml.tuple [PathName.pp o])

  (** Pretty-print an open construct to Coq. *)
  let to_coq (o : t): SmartPrint.t =
    nest (!^ "Require Import" ^^ PathName.to_coq o ^-^ !^ ".")
end
*)

(** A structure. *)
type ('a, 'b) t =
  | Value of Loc.t * 'a * 'b Value.t
  | Inductive of Loc.t * Inductive.t
  | Record of Loc.t * Record.t
  | Synonym of Loc.t * Synonym.t
  | Exception of Loc.t * Exception.t
  | Reference of Loc.t * Reference.t
  (* | Open of Loc.t * Open.t *)
  | Module of Loc.t * Name.t * ('a, 'b) t list

let rec pp (pp_a : 'a -> SmartPrint.t) (pp_b : 'b -> SmartPrint.t)
  (defs : ('a, 'b) t list) : SmartPrint.t =
  let pp_one (def : ('a, 'b) t) : SmartPrint.t =
    match def with
    | Value (loc, a, value) ->
      Loc.pp loc ^^ OCaml.tuple [pp_a a; Value.pp pp_b value]
    | Inductive (loc, ind) -> Loc.pp loc ^^ Inductive.pp ind
    | Record (loc, record) -> Loc.pp loc ^^ Record.pp record
    | Synonym (loc, synonym) -> Loc.pp loc ^^ Synonym.pp synonym
    | Exception (loc, exn) -> Loc.pp loc ^^ Exception.pp exn
    | Reference (loc, r) -> Loc.pp loc ^^ Reference.pp r
    (* | Open (loc, o) -> Loc.pp loc ^^ Open.pp o *)
    | Module (loc, name, defs) ->
      nest (
        Loc.pp loc ^^ !^ "Module" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
        indent (pp pp_a pp_b defs)) in
  separate (newline ^^ newline) (List.map pp_one defs)

(** Import an OCaml structure. *)
let rec of_structure (env : unit FullEnvi.t) (structure : structure)
  : unit FullEnvi.t * (unit, Loc.t) t list =
  let of_structure_item (env : unit FullEnvi.t) (item : structure_item)
    : unit FullEnvi.t * (unit, Loc.t) t =
    let loc = Loc.of_location item.str_loc in
    match item.str_desc with
    | Tstr_value (_, [{vb_pat = {pat_desc = Tpat_var (x, _)};
      vb_expr = {
        exp_desc = Texp_apply ({exp_desc = Texp_ident (path, _, _)}, [_]);
        exp_type = {Types.desc = Types.Tconstr (_, [typ], _)}}}])
      when PathName.of_path path = PathName.of_name ["Pervasives"] "ref" ->
      let r = {
        Reference.name = Name.of_ident x;
        typ = Type.of_type_expr env typ } in
      (Reference.update_env r env, Reference (loc, r))
    | Tstr_value (is_rec, [{
      vb_pat = pattern; vb_expr = e;
      vb_attributes = attrs}]) ->
      let (env, is_rec, pattern, typ_vars, args, typ, e) =
        Exp.import_let_fun env is_rec pattern e in
      (match pattern with
      | Pattern.Variable x ->
        (env, Value (loc, (), {
          Value.header = (is_rec, Attribute.of_attributes attrs, x, typ_vars, args, Some typ);
          body = e }))
      | _ -> Error.raise loc "Cannot match a function definition on a pattern.")
    | Tstr_type [{typ_id = name; typ_type = typ}] ->
      let name = Name.of_ident name in
      let typ_vars = List.map Type.of_type_expr_variable typ.type_params in
      (match typ.type_kind with
      | Type_variant cases ->
        let constructors =
          let env = FullEnvi.add_typ [] name env in
          cases |> List.map (fun {cd_id = constr; cd_args = typs} ->
            (Name.of_ident constr, typs |> List.map (fun typ ->
              Type.of_type_expr env typ))) in
        let ind = {
          Inductive.name = name;
          typ_vars = typ_vars;
          constructors = constructors } in
        (Inductive.update_env ind env, Inductive (loc, ind))
      | Type_record (fields, _) ->
        let fields = fields |> List.map (fun {ld_id = x; ld_type = typ} ->
          (Name.of_ident x, Type.of_type_expr env typ)) in
        let r = {
          Record.name = name;
          fields = fields } in
        (Record.update_env r env, Record (loc, r))
      | Type_abstract ->
        (match typ.type_manifest with
        | Some typ ->
          let syn = {
            Synonym.name = name;
            typ_vars = typ_vars;
            value = Type.of_type_expr env typ } in
          (Synonym.update_env syn env, Synonym (loc, syn))
        | None -> Error.raise loc "Type definition not handled."))
    | Tstr_exception { cd_id = name; cd_args = args } ->
      let name = Name.of_ident name in
      let typ =
        Type.Tuple (args |> List.map (fun { ctyp_type = typ } ->
          Type.of_type_expr env typ)) in
      let exn = { Exception.name = name; typ = typ} in
      (Exception.update_env exn env, Exception (loc, exn))
    (* | Tstr_open (_, path, _, _) -> (Error.raise loc "TODO", Open (PathName.of_path 0 path)) *)
    | Tstr_module {mb_id = name;
      mb_expr = { mod_desc = Tmod_structure structure }} ->
      let name = Name.of_ident name in
      let env = FullEnvi.open_module env in
      let (env, structures) = of_structure env structure in
      let env = FullEnvi.close_module env name in
      (env, Module (loc, name, structures))
    | _ -> Error.raise loc "Structure item not handled." in
  let (env, defs) =
    List.fold_left (fun (env, defs) item ->
      let (env, def) = of_structure_item env item in
      (env, def :: defs))
    (env, []) structure.str_items in
  (env, List.rev defs)

let rec monadise_let_rec (env : unit FullEnvi.t) (defs : (unit, Loc.t) t list)
  : unit FullEnvi.t * (unit, Loc.t) t list =
  let rec monadise_let_rec_one (env : unit FullEnvi.t) (def : (unit, Loc.t) t)
    : unit FullEnvi.t * (unit, Loc.t) t list =
    match def with
    | Value (loc, (), { Value.header = header; body = body }) ->
      let (env, defs) = Exp.monadise_let_rec_definition env header body in
      (env, defs |> List.rev |> List.map (fun (header, body) ->
        Value (loc, (), { Value.header = header; body = body })))
    | Module (loc, name, defs) ->
      let env = FullEnvi.open_module env in
      let (env, defs) = monadise_let_rec env defs in
      let env = FullEnvi.close_module env name in
      (env, [Module (loc, name, defs)])
    | Inductive (loc, ind) -> (Inductive.update_env ind env, [def])
    | Record (loc, record) -> (Record.update_env record env, [def])
    | Synonym (loc, synonym) -> (Synonym.update_env synonym env, [def])
    | Exception (loc, exn) -> (Exception.update_env exn env, [def])
    | Reference (loc, r) -> (Reference.update_env r env, [def]) in
  let (env, defs) = List.fold_left (fun (env, defs) def ->
    let (env, defs') = monadise_let_rec_one env def in
    (env, defs' @ defs))
    (env, []) defs in
  (env, List.rev defs)

let rec effects (env : Effect.Type.t FullEnvi.t) (defs : (unit, 'a) t list)
  : Effect.Type.t FullEnvi.t * (Effect.Type.t, 'a * Effect.t) t list =
  let rec effects_one (env : Effect.Type.t FullEnvi.t) (def : (unit, 'a) t)
    : Effect.Type.t FullEnvi.t * (Effect.Type.t, 'a * Effect.t) t =
    match def with
    | Value (loc, (), {
      Value.header = (is_rec, _, x, _, args, _) as header;
      body = e }) ->
      let (e, x_typ) = Exp.effects_of_let env is_rec x args e in
      let descriptor = (snd (Exp.annotation e)).Effect.descriptor in
      if Effect.Descriptor.is_pure descriptor || args <> [] then
        let value = { Value.header = header; body = e } in
        (Value.update_env value x_typ env, Value (loc, x_typ, value))
      else
        failwith "Effects unexpected for toplevel values."
    | Module (loc, name, defs) ->
      let env = FullEnvi.open_module env in
      let (env, defs) = effects env defs in
      let env = FullEnvi.close_module env name in
      (env, Module (loc, name, defs))
    | Exception (loc, exn) ->
      (Exception.update_env_with_effects exn env loc, Exception (loc, exn))
    | Reference (loc, r) ->
      (Reference.update_env_with_effects r env loc, Reference (loc, r))
    | Inductive (loc, ind) -> (Inductive.update_env ind env, Inductive (loc, ind))
    | Record (loc, record) -> (Record.update_env record env, Record (loc, record))
    | Synonym (loc, synonym) -> (Synonym.update_env synonym env, Synonym (loc, synonym)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env, def) =
        effects_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

let rec monadise (env : unit Envi.t)
  (defs : (Effect.Type.t, Loc.t * Effect.t) t list)
  : unit Envi.t * (unit, Loc.t) t list =
  let rec monadise_one (env : unit Envi.t)
    (def : (Effect.Type.t, Loc.t * Effect.t) t)
    : unit Envi.t * (unit, Loc.t) t =
    match def with
    | Value (loc, effect, {
      Value.header = (is_rec, attr, x, typ_vars, args, typ);
      body = body }) ->
      let typ = match typ with
        | None -> None
        | Some typ -> Some (Type.monadise typ (snd (Exp.annotation body))) in
      let env_in_body =
        if Recursivity.to_bool is_rec then
          Envi.add_name x () env
        else
          env in
      let env_in_body =
        List.fold_left (fun env_in_body (x, _) -> Envi.add_name x () env_in_body)
          env_in_body args in
      let body = Exp.monadise env_in_body body in
      let env = Envi.add_name x () env in
      (env, Value (loc, (), {
        Value.header = (is_rec, attr, x, typ_vars, args, typ);
        body = body }))
    | Module (loc, name, defs) ->
      let (env, defs) = monadise (Envi.open_module env) defs in
      (Envi.close_module env (fun _ _ -> ()) name, Module (loc, name, defs))
    | Exception (loc, exn) ->
      (Envi.add_name exn.Exception.name () env, Exception (loc, exn))
    | Reference (loc, r) ->
      (Envi.add_name r.Reference.name () env, Reference (loc, r))
    | Inductive (loc, ind) -> (env, Inductive (loc, ind))
    | Record (loc, record) -> (env, Record (loc, record))
    | Synonym (loc, synonym) -> (env, Synonym (loc, synonym)) in
  let (env, defs) =
    List.fold_left (fun (env, defs) def ->
      let (env_units, def) = monadise_one env def in
      (env, def :: defs))
      (env, []) defs in
  (env, List.rev defs)

(** Pretty-print a structure to Coq. *)
let rec to_coq (defs : ('a, 'b) t list) : SmartPrint.t =
  let to_coq_one (def : ('a, 'b) t) : SmartPrint.t =
    match def with
    | Value (_, _, value) -> Value.to_coq value
    | Inductive (_, ind) -> Inductive.to_coq ind
    | Record (_, record) -> Record.to_coq record
    | Synonym (_, s) -> Synonym.to_coq s
    | Exception (_, exn) -> Exception.to_coq exn
    | Reference (_, r) -> Reference.to_coq r
    (* | Open o -> Open.to_coq o *)
    | Module (_, name, defs) ->
      nest (
        !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
        indent (to_coq defs) ^^ newline ^^
        !^ "End" ^^ Name.to_coq name ^-^ !^ ".") in
  separate (newline ^^ newline) (List.map to_coq_one defs)
