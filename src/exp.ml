open Typedtree
(** An expression. *)

open SmartPrint
open Monad.Notations

module Header = struct
  type t = {
    name : Name.t;
    typ_vars : VarEnv.t;
    args : (Name.t * Type.t) list;
    structs : string list;
    typ : Type.t;
    is_notation : bool;
  }

  let to_coq_structs (header : t) : SmartPrint.t =
    match header.structs with
    | [] -> empty
    | _ :: _ ->
        let structs = separate space (List.map (fun s -> !^s) header.structs) in
        braces (nest (!^"struct" ^^ structs))
end

module Definition = struct
  type 'a t = { is_rec : Recursivity.t; cases : (Header.t * 'a) list }
end

type match_existential_cast = {
  new_typ_vars : VarEnv.t;
  bound_vars : (Name.t * Type.t) list;
  return_typ : Type.t;
  use_axioms : bool;
  cast_result : bool;
  enable : bool;
}

type dependent_pattern_match = {
  cast : Type.t;
  motive : Type.t;
  args : Type.t list;
}

(** The simplified OCaml AST we use. We do not use a mutualy recursive type to
    simplify the importation in Coq. *)
type t =
  | Constant of Constant.t
  | Variable of MixedPath.t * (string * string) list
  | Tuple of t list  (** A tuple of expressions. *)
  | Constructor of PathName.t * (string * string) list * t list
      (** A constructor name, some implicits, and a list of arguments. *)
  | ConstructorExtensible of string * Type.t * t
      (** A constructor of an extensible type, with a tag and a payload. *)
  | ConstructorVariant of string * (Type.t * t) option
      (** A constructor of polymorphic variant, with a tag and a payload. *)
  | Apply of t * t option list  (** An application. *)
  | Return of string * t  (** Application specialized for a return operation. *)
  | InfixOperator of string * t * t
      (** Application specialized for an infix operator.
        An argument name, an optional type and a body. *)
  | Function of Name.t * Type.t option * t
  | Functions of Name.t list * t  (** An argument names and a body. *)
  | LetVar of string option * Name.t * Name.t list * t * t
      (** The let of a variable, with optionally a list of polymorphic variables.
        We optionally specify the symbol of the let operator as it may be
        non-standard for monadic binds. *)
  | LetFun of t option Definition.t * t
  | LetTyp of Name.t * Name.t list * Type.t * t
      (** The definition of a type. It is used to represent module values. *)
  | LetModuleUnpack of Name.t * PathName.t * t
      (** Open a first-class module. *)
  | Match of
      t
      * dependent_pattern_match option
      * (Pattern.t * match_existential_cast option * t) list
      * bool  (** Match an expression to a list of patterns. *)
  | MatchExtensible of t * ((string * Pattern.t * Type.t) option * t) list
      (** Match an expression on a list of extensible type patterns. *)
  | Record of (PathName.t * int * t) list
      (** Construct a record giving an expression for each field. *)
  | Field of t * PathName.t  (** Access to a field of a record. *)
  | IfThenElse of t * t * t  (** The "else" part may be unit. *)
  | Module of (PathName.t * int * t) list
      (** The value of a first-class module. *)
  | ModulePack of (int Tree.t * t)  (** Pack a module. *)
  | Functor of Name.t * Type.t * t  (** A functor. *)
  | Cast of t * Type.t  (** Force the cast to a type (with an axiom). *)
  | TypAnnotation of t * Type.t  (** Annotate an expression by its type. *)
  | Assert of Type.t * t  (** The assert keyword. *)
  | Error of string  (** An error message for unhandled expressions. *)
  | ErrorArray of t list  (** An error produced by an array of elements. *)
  | ErrorTyp of Type.t  (** An error composed of a type. *)
  | ErrorMessage of t * string
      (** An expression together with an error message. *)
  | Ltac of ltac

and ltac = Subst | Discriminate | Exact of t | Concat of ltac * ltac

(** Take a function expression and make explicit the list of arguments and
    the body. *)
let rec open_function (e : t) : Name.t list * t =
  match e with
  | Function (x, _, e) ->
      let xs, e = open_function e in
      (x :: xs, e)
  | _ -> ([], e)

let error_message (e : t) (category : Error.Category.t) (message : string) :
    t Monad.t =
  raise (ErrorMessage (e, message)) category message

let error_message_in_module (field : Name.t option) (e : t)
    (category : Error.Category.t) (message : string) :
    (string option * Name.t option * t) option Monad.t =
  raise (Some (Some message, field, e)) category message

module ModuleTypValues = struct
  type t = Module of Name.t * int | Value of Name.t * int

  let get (typ_vars : Name.t Name.Map.t) (module_typ : Types.module_type) :
      t list Monad.t =
    get_env >>= fun env ->
    match Env.scrape_alias env module_typ with
    | Mty_signature signature ->
        signature
        |> Monad.List.filter_map (fun item ->
               match item with
               | Types.Sig_value (ident, { val_type; _ }, _) ->
                   let* ident = Name.of_ident true ident in
                   Type.of_typ_expr true typ_vars val_type
                   >>= fun (_, _, new_typ_vars) ->
                   return (Some (Value (ident, List.length new_typ_vars)))
               | Sig_module (ident, _, _, _, _)
                 when Ident.name ident = "Internal_for_tests" ->
                   return None
               | Sig_module (ident, _, { Types.md_type; _ }, _, _) ->
                   let* name = Name.of_ident false ident in
                   let* arity =
                     ModuleTypParams.get_functor_nb_free_vars_params md_type
                   in
                   return (Some (Module (name, arity)))
               | _ -> return None)
    | _ -> raise [] Unexpected "Module type signature not found"
end

let dependent_transform (e : t) (dep_match : dependent_pattern_match option) =
  match dep_match with
  | None -> e
  | Some { args; _ } ->
      let args =
        args
        |> List.mapi (fun i _ -> "eq" ^ string_of_int i |> Name.of_string_raw)
      in
      let e = Ltac (Concat (Subst, Exact e)) in
      Functions (args, e)

let rec any_patterns_with_ith_true (is_guarded : bool) (i : int) (n : int) :
    Pattern.t list =
  if n = 0 then []
  else
    let head =
      if i = 0 && is_guarded then Pattern.Constructor (PathName.true_value, [])
      else Pattern.Any
    in
    head :: any_patterns_with_ith_true is_guarded (i - 1) (n - 1)

let rec get_include_name (module_expr : module_expr) : Name.t Monad.t =
  match module_expr.mod_desc with
  | Tmod_apply (applied_expr, _, _) -> (
      match applied_expr.mod_desc with
      | Tmod_ident (path, _)
      | Tmod_constraint ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
          let* path_name = PathName.of_path_with_convert false path in
          let* name = PathName.to_name false path_name in
          return (Name.suffix_by_include name)
      | _ -> get_include_name applied_expr)
  | Tmod_constraint (module_expr, _, _, _) -> get_include_name module_expr
  | _ ->
      raise
        (Name.of_string_raw "nameless_include")
        NotSupported
        ("Cannot find a name for this module expression.\n\n"
       ^ "Try to first give a name to this module before doing the include.")

let build_module (_ : int Tree.t) (values : ModuleTypValues.t list)
    (signature_path : Path.t)
    (mixed_path_of_value_or_typ : Name.t -> MixedPath.t Monad.t) : t Monad.t =
  let* fields =
    values
    |> Monad.List.map (function
         | ModuleTypValues.Value (value, nb_free_vars) ->
             let* field_name =
               PathName.of_path_and_name_with_convert signature_path value
             in
             let* mixed_path = mixed_path_of_value_or_typ value in
             return (field_name, nb_free_vars, Variable (mixed_path, []))
         | Module (name, arity) ->
             let* field_name =
               PathName.of_path_and_name_with_convert signature_path name
             in
             let* mixed_path = mixed_path_of_value_or_typ name in
             return (field_name, arity, Variable (mixed_path, [])))
  in
  return (Module fields)

let rec bind_existentials (existentials : Name.t list) (typ : Type.t) : Type.t =
  let name = Name.of_string_raw "fst" in
  let fst = Type.build_apply_from_name MixedPath.prim_proj_fst name in
  let snd = Type.build_apply_from_name MixedPath.prim_proj_snd name in
  match existentials with
  | [] -> typ
  | [ x ] -> Type.Let (x, Variable name, typ)
  | [ x; y ] -> Type.Let (x, snd, Type.Let (y, fst, typ))
  | x :: xs ->
      let typ = bind_existentials xs typ in
      Type.Let (x, snd, Type.Let (name, fst, typ))

let build_existential_return (existentials : Name.t list) (typ : Type.t) :
    Type.t =
  let fst = Name.of_string_raw "fst" in
  let exi = Name.of_string_raw "exi" in
  let exityp = Type.build_apply_from_name MixedPath.projT1 exi in
  let typ = bind_existentials (List.rev existentials) typ in
  Type.Let (fst, exityp, typ)

let rec smart_return (operator : string) (e : t) : t Monad.t =
  match e with
  | Return (operator2, e2) -> (
      let* configuration = get_configuration in
      match
        Configuration.is_in_merge_returns configuration operator operator2
      with
      | None -> return (Return (operator, e))
      | Some target -> return (Return (target, e2)))
  | LetVar (None, x, typ_params, e1, e2) ->
      let* e2 = smart_return operator e2 in
      return (LetVar (None, x, typ_params, e1, e2))
  | Match (e, dep_match, cases, is_with_default_case) ->
      let* cases =
        cases
        |> Monad.List.map (fun (p, existential_cast, e) ->
               let* e = smart_return operator e in
               return (p, existential_cast, e))
      in
      return (Match (e, dep_match, cases, is_with_default_case))
  | _ -> return (Return (operator, e))

(** The free exitential type variables in an expression. This is useful to know
    in the match which exitential types are actually used, so that unused
    existential types are not printed. *)
let rec free_existential_typs (e : t) : Name.Set.t =
  let of_list (es : t list) : Name.Set.t =
    List.fold_left Name.Set.union Name.Set.empty
      (List.map free_existential_typs es)
  in
  let of_definition (definition : t option Definition.t) : Name.Set.t =
    let { Definition.cases; _ } = definition in
    let free_typs_list =
      cases
      |> List.map (fun ({ Header.typ_vars; args; typ; _ }, body) ->
             let typs = List.map snd args in
             let es = match body with None -> [] | Some body -> [ body ] in
             Name.Set.diff
               (Name.Set.union
                  (Type.local_typ_constructors_of_typs (typ :: typs))
                  (of_list es))
               (Name.Set.of_list (List.map fst typ_vars)))
    in
    List.fold_left Name.Set.union Name.Set.empty free_typs_list
  in
  let of_implicits (implicits : (string * string) list) : Name.Set.t =
    Name.Set.of_list
      (List.map (fun (_, typ) -> Name.of_string_raw typ) implicits)
  in
  match e with
  | Constant _ -> Name.Set.empty
  | Variable (_, implicits) -> of_implicits implicits
  | Tuple es -> of_list es
  | Constructor (_, implicits, es) ->
      Name.Set.union (of_implicits implicits) (of_list es)
  | ConstructorExtensible (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | ConstructorVariant (_, typ_e) -> (
      match typ_e with
      | None -> Name.Set.empty
      | Some (typ, e) ->
          Name.Set.union
            (Type.local_typ_constructors_of_typ typ)
            (free_existential_typs e))
  | Apply (e, es) ->
      let es = e :: List.filter_map (fun x -> x) es in
      of_list es
  | Return (_, e) -> free_existential_typs e
  | InfixOperator (_, e1, e2) -> of_list [ e1; e2 ]
  | Function (_, typ, e) ->
      let typs = match typ with None -> [] | Some typ -> [ typ ] in
      Name.Set.union
        (Type.local_typ_constructors_of_typs typs)
        (free_existential_typs e)
  | Functions (_, e) -> free_existential_typs e
  | LetVar (_, _, typ_vars, e1, e2) ->
      Name.Set.diff (of_list [ e1; e2 ]) (Name.Set.of_list typ_vars)
  | LetFun (definition, e) ->
      Name.Set.union (of_definition definition) (free_existential_typs e)
  | LetTyp (name, typ_vars, typ, e) ->
      Name.Set.union
        (Name.Set.diff
           (Type.local_typ_constructors_of_typ typ)
           (Name.Set.of_list typ_vars))
        (Name.Set.remove name (free_existential_typs e))
  | LetModuleUnpack (_, _, e) -> free_existential_typs e
  | Match (e, _, cases, _) ->
      let cast_typs =
        cases
        |> List.map (fun (_, cast, e) ->
               let new_typ_vars =
                 match cast with
                 | Some { bound_vars; enable = true; _ } ->
                     Name.Set.of_list (List.map fst bound_vars)
                 | _ -> Name.Set.empty
               in
               let typ_vars_of_typs =
                 match cast with
                 | Some
                     { bound_vars; return_typ; cast_result; enable = true; _ }
                   ->
                     Type.local_typ_constructors_of_typs
                       ((if cast_result then [ return_typ ] else [])
                       @ List.map snd bound_vars)
                 | _ -> Name.Set.empty
               in
               Name.Set.diff
                 (Name.Set.union typ_vars_of_typs (free_existential_typs e))
                 new_typ_vars)
      in
      List.fold_left Name.Set.union Name.Set.empty
        (free_existential_typs e :: cast_typs)
  | MatchExtensible (e1, cases) ->
      let es = e1 :: List.map snd cases in
      let typs =
        cases
        |> List.filter_map (fun (pattern, _) ->
               match pattern with None -> None | Some (_, _, typ) -> Some typ)
      in
      Name.Set.union (of_list es) (Type.local_typ_constructors_of_typs typs)
  | Record items ->
      let es = List.map (fun (_, _, e) -> e) items in
      of_list es
  | Field (e, _) -> free_existential_typs e
  | IfThenElse (e1, e2, e3) -> of_list [ e1; e2; e3 ]
  | Module items ->
      let es = List.map (fun (_, _, e) -> e) items in
      of_list es
  | ModulePack (_, e) -> free_existential_typs e
  | Functor (_, typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Cast (e, typ) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | TypAnnotation (e, typ) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Assert (typ, e) ->
      Name.Set.union
        (Type.local_typ_constructors_of_typ typ)
        (free_existential_typs e)
  | Error _ -> Name.Set.empty
  | ErrorArray es -> of_list es
  | ErrorTyp typ -> Type.local_typ_constructors_of_typ typ
  | ErrorMessage (e, _) -> free_existential_typs e
  | Ltac _ -> Name.Set.empty

(** Get the free variables of an expression. This is useful to optimize the
    translation of mutually recursive definitions implemented as notation,
    by detecting which ones are used. *)
let rec get_free_vars (e : t) : Name.Set.t =
  let get_free_vars_of_list (es : t list) : Name.Set.t =
    List.fold_left Name.Set.union Name.Set.empty (List.map get_free_vars es)
  in
  match e with
  | Constant _ -> Name.Set.empty
  | Variable (x, _) -> (
      match x with
      | MixedPath.PathName { path = []; base } -> Name.Set.singleton base
      | _ -> Name.Set.empty)
  | Tuple es -> get_free_vars_of_list es
  | Constructor (_, _, es) -> get_free_vars_of_list es
  | ConstructorExtensible (_, _, e) -> get_free_vars e
  | ConstructorVariant (_, typ_e) -> (
      match typ_e with None -> Name.Set.empty | Some (_, e) -> get_free_vars e)
  | Apply (e, es) ->
      let es = e :: List.filter_map (fun x -> x) es in
      get_free_vars_of_list es
  | Return (_, e) -> get_free_vars e
  | InfixOperator (_, e1, e2) -> get_free_vars_of_list [ e1; e2 ]
  | Function (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Functions (names, e) ->
      Name.Set.diff (get_free_vars e) (Name.Set.of_list names)
  | LetVar (_, x, _, e1, e2) ->
      Name.Set.union (get_free_vars e1) (Name.Set.remove x (get_free_vars e2))
  | LetFun (definition, e) ->
      let defined_names =
        definition.cases |> List.map (fun ({ Header.name; _ }, _) -> name)
      in
      let is_rec = definition.is_rec in
      let free_vars_of_bodies =
        definition.cases
        |> List.map (fun ({ Header.args; _ }, body) ->
               match body with
               | None -> Name.Set.empty
               | Some body ->
                   Name.Set.diff (get_free_vars body)
                     (Name.Set.of_list (List.map fst args)))
      in
      let free_vars_of_definition =
        Name.Set.diff
          (List.fold_left Name.Set.union Name.Set.empty free_vars_of_bodies)
          (if is_rec then Name.Set.of_list defined_names else Name.Set.empty)
      in
      Name.Set.union free_vars_of_definition
        (Name.Set.diff (get_free_vars e) (Name.Set.of_list defined_names))
  | LetTyp (_, _, _, e) -> get_free_vars e
  | LetModuleUnpack (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Match (e, _, entries, _) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, _, e) ->
                  Name.Set.diff (get_free_vars e)
                    (Pattern.get_free_vars pattern))))
  | MatchExtensible (e, entries) ->
      Name.Set.union (get_free_vars e)
        (List.fold_left Name.Set.union Name.Set.empty
           (entries
           |> List.map (fun (pattern, e) ->
                  let free_vars_of_pattern =
                    match pattern with
                    | Some (_, pattern, _) -> Pattern.get_free_vars pattern
                    | None -> Name.Set.empty
                  in
                  Name.Set.diff (get_free_vars e) free_vars_of_pattern)))
  | Record entries ->
      get_free_vars_of_list (List.map (fun (_, _, e) -> e) entries)
  | Field (e, _) -> get_free_vars e
  | IfThenElse (e1, e2, e3) -> get_free_vars_of_list [ e1; e2; e3 ]
  | Module entries ->
      get_free_vars_of_list (List.map (fun (_, _, e) -> e) entries)
  | ModulePack (_, e) -> get_free_vars e
  | Functor (x, _, e) -> Name.Set.remove x (get_free_vars e)
  | Cast (e, _) -> get_free_vars e
  | TypAnnotation (e, _) -> get_free_vars e
  | Assert (_, e) -> get_free_vars e
  | Error _ -> Name.Set.empty
  | ErrorArray es -> get_free_vars_of_list es
  | ErrorTyp _ -> Name.Set.empty
  | ErrorMessage (e, _) -> get_free_vars e
  | Ltac _ -> Name.Set.empty

(** Import an OCaml expression. *)
let rec of_expression (typ_vars : Name.t Name.Map.t) (e : expression) :
    t Monad.t =
  set_env e.exp_env
    (set_loc e.exp_loc
       (let* attributes = Attribute.of_attributes e.exp_attributes in
        let typ = e.exp_type in
        (* We do not indent here to preserve the diff. *)
        let* e =
          match e.exp_desc with
          | Texp_ident (path, _, _) ->
              let implicits = Attribute.get_implicits attributes in
              let* x = MixedPath.of_path true path in
              return (Variable (x, implicits))
          | Texp_constant constant ->
              Constant.of_constant constant >>= fun constant ->
              return (Constant constant)
          | Texp_let (is_rec, cases, e2) ->
              of_expression typ_vars e2 >>= fun e2 ->
              of_let typ_vars is_rec cases e2
          | Texp_function
              {
                cases =
                  [
                    {
                      c_lhs = { pat_desc = Tpat_var (x, _); pat_type; _ };
                      c_rhs = e;
                      _;
                    };
                  ];
                _;
              }
          | Texp_function
              {
                cases =
                  [
                    {
                      c_lhs =
                        {
                          pat_desc =
                            Tpat_alias ({ pat_desc = Tpat_any; _ }, x, _);
                          pat_type;
                          _;
                        };
                      c_rhs = e;
                      _;
                    };
                  ];
                _;
              } ->
              let* x = Name.of_ident true x in
              let* typ, _, _ = Type.of_typ_expr true typ_vars pat_type in
              of_expression typ_vars e >>= fun e ->
              return (Function (x, Some typ, e))
          | Texp_function { cases; _ } ->
              let is_gadt_match =
                Attribute.has_match_gadt attributes
                || Attribute.has_match_gadt_with_result attributes
              in
              let is_tagged_match = Attribute.has_tagged_match attributes in
              let do_cast_results =
                Attribute.has_match_gadt_with_result attributes
              in
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              let is_grab_existentials =
                Attribute.has_grab_existentials attributes
              in
              let* x, typ, e =
                open_cases typ_vars cases is_gadt_match is_tagged_match
                  do_cast_results is_with_default_case is_grab_existentials
              in
              return (Function (x, typ, e))
          | Texp_apply (e_f, e_xs) -> (
              of_expression typ_vars e_f >>= fun e_f ->
              e_xs
              |> Monad.List.map (fun (_, e_x) ->
                     match e_x with
                     | Some e_x ->
                         of_expression typ_vars e_x >>= fun e_x ->
                         return (Some e_x)
                     | None -> return None)
              >>= fun e_xs ->
              (* We consider the OCaml's [@@] and [|>] operators as syntactic sugar. *)
              let e_f, e_xs =
                match (e_f, e_xs) with
                | ( Variable
                      ( MixedPath.PathName
                          {
                            PathName.path =
                              [ Name.Make ("Pervasives" | "Stdlib") ];
                            base = Name.Make "op_atat";
                          },
                        [] ),
                    [ Some f; x ] ) ->
                    (f, [ x ])
                | ( Variable
                      ( MixedPath.PathName
                          {
                            PathName.path =
                              [ Name.Make ("Pervasives" | "Stdlib") ];
                            base = Name.Make "op_pipegt";
                          },
                        [] ),
                    [ x; Some f ] ) ->
                    (f, [ x ])
                | _ -> (e_f, e_xs)
              in
              (* We introduce a monadic notation according to the configuration. *)
              let* configuration = get_configuration in
              let apply_with_let =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match Configuration.is_monadic_let configuration name with
                    | Some let_symbol ->
                        Some (LetVar (Some let_symbol, x, [], e1, e2))
                    | None -> None)
                | _ -> None
              in
              let* apply_with_let_return =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_let_return configuration name
                    with
                    | Some (let_symbol, return_notation) ->
                        let* return_e2 = smart_return return_notation e2 in
                        return
                          (Some (LetVar (Some let_symbol, x, [], e1, return_e2)))
                    | None -> return None)
                | _ -> return None
              in
              let* apply_with_return =
                match (e_f, e_xs) with
                | Variable (MixedPath.PathName path_name, []), [ Some e ] -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_return configuration name
                    with
                    | Some return_notation ->
                        let* return_e = smart_return return_notation e in
                        return (Some return_e)
                    | None -> return None)
                | _ -> return None
              in
              let* apply_with_return_let =
                match (e_f, e_xs) with
                | ( Variable (MixedPath.PathName path_name, []),
                    [ Some e1; Some (Function (x, _, e2)) ] ) -> (
                    let name = PathName.to_string path_name in
                    match
                      Configuration.is_monadic_return_let configuration name
                    with
                    | Some (return_notation, let_symbol) ->
                        let* return_e1 = smart_return return_notation e1 in
                        return
                          (Some (LetVar (Some let_symbol, x, [], return_e1, e2)))
                    | None -> return None)
                | _ -> return None
              in
              let apply_with_infix_operator =
                match (e_f, e_xs) with
                | Variable (mixed_path, []), [ Some e1; Some e2 ] -> (
                    let name = MixedPath.to_string mixed_path in
                    match
                      Configuration.is_operator_infix configuration name
                    with
                    | None -> None
                    | Some operator -> Some (InfixOperator (operator, e1, e2)))
                | _ -> None
              in
              let applies =
                [
                  apply_with_let;
                  apply_with_let_return;
                  apply_with_return;
                  apply_with_return_let;
                  apply_with_infix_operator;
                ]
              in
              match List.find_map (fun x -> x) applies with
              | Some apply -> return apply
              | None -> return (Apply (e_f, e_xs)))
          | Texp_match (e, cases, _) ->
              let is_gadt_match =
                Attribute.has_match_gadt attributes
                || Attribute.has_match_gadt_with_result attributes
              in
              let is_tagged_match = Attribute.has_tagged_match attributes in
              let do_cast_results =
                Attribute.has_match_gadt_with_result attributes
              in
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              let is_grab_existential =
                Attribute.has_grab_existentials attributes
              in
              let* e = of_expression typ_vars e in
              of_match typ_vars e cases is_gadt_match is_tagged_match
                do_cast_results is_with_default_case is_grab_existential
          | Texp_tuple es ->
              Monad.List.map (of_expression typ_vars) es >>= fun es ->
              return (Tuple es)
          | Texp_construct (_, constructor_description, es) -> (
              let* es' = Monad.List.map (of_expression typ_vars) es in
              match constructor_description.cstr_tag with
              | Cstr_extension (path, _) ->
                  let* typs =
                    es
                    |> Monad.List.map (fun { exp_type; _ } ->
                           Type.of_type_expr_without_free_vars exp_type)
                  in
                  let typ = Type.Tuple typs in
                  let e = Tuple es' in
                  return (ConstructorExtensible (Path.last path, typ, e))
              | _ ->
                  let implicits = Attribute.get_implicits attributes in
                  let* x =
                    PathName.of_constructor_description constructor_description
                  in
                  return (Constructor (x, implicits, es')))
          | Texp_variant (label, e) -> (
              let* path_name = PathName.constructor_of_variant label in
              match path_name with
              | None ->
                  let* typ_e =
                    match e with
                    | None -> return None
                    | Some e ->
                        let* typ =
                          Type.of_type_expr_without_free_vars e.exp_type
                        in
                        let* e = of_expression typ_vars e in
                        return (Some (typ, e))
                  in
                  return (ConstructorVariant (label, typ_e))
              | Some path_name -> (
                  let constructor =
                    Variable (MixedPath.PathName path_name, [])
                  in
                  match e with
                  | None -> return constructor
                  | Some e ->
                      let* e = of_expression typ_vars e in
                      return (Apply (constructor, [ Some e ]))))
          | Texp_record { fields; extended_expression; _ } -> (
              Array.to_list fields
              |> Monad.List.filter_map (fun (label_description, definition) ->
                     (match definition with
                     | Kept _ -> return None
                     | Overridden (_, e) ->
                         PathName.of_label_description label_description
                         >>= fun x ->
                         let* typ =
                           Type.of_type_expr_without_free_vars
                             label_description.lbl_arg
                         in
                         let arity = Type.nb_forall_typs typ in
                         return (Some (x, arity, e)))
                     >>= fun x_e ->
                     match x_e with
                     | None -> return None
                     | Some (x, arity, e) ->
                         of_expression typ_vars e >>= fun e ->
                         return (Some (x, arity, e)))
              >>= fun fields ->
              match extended_expression with
              | None -> return (Record fields)
              | Some extended_expression ->
                  of_expression typ_vars extended_expression
                  >>= fun extended_e ->
                  return
                    (List.fold_left
                       (fun extended_e (x, _, e) ->
                         Apply
                           ( Variable
                               ( MixedPath.PathName (PathName.prefix_by_with x),
                                 [] ),
                             [ Some e; Some extended_e ] ))
                       extended_e fields))
          | Texp_field (e, _, label_description) ->
              PathName.of_label_description label_description >>= fun x ->
              of_expression typ_vars e >>= fun e -> return (Field (e, x))
          | Texp_ifthenelse (e1, e2, e3) ->
              of_expression typ_vars e1 >>= fun e1 ->
              of_expression typ_vars e2 >>= fun e2 ->
              (match e3 with
              | None -> return (Tuple [])
              | Some e3 -> of_expression typ_vars e3)
              >>= fun e3 -> return (IfThenElse (e1, e2, e3))
          | Texp_sequence (e1, e2) ->
              let* e1 = of_expression typ_vars e1 in
              let* e2 = of_expression typ_vars e2 in
              return (Match (e1, None, [ (Pattern.Any, None, e2) ], false))
          | Texp_try (e, cases) -> (
              let* e = of_expression typ_vars e in
              let default_error =
                error_message (Error "typ_with_with_non_trivial_matching")
                  SideEffect
                  ("Use a trivial matching for the `with` clause, like:\n"
                 ^ "\n" ^ "    try ... with exn -> ...\n" ^ "\n"
                 ^ "You can do a second matching on `exn` in the error handler \
                    if needed.")
              in
              match cases with
              | [ { c_lhs; c_rhs; _ } ] -> (
                  let* name =
                    match c_lhs.pat_desc with
                    | Tpat_var (ident, _) ->
                        let* name = Name.of_ident true ident in
                        return (Some name)
                    | Tpat_any -> return (Some Name.Nameless)
                    | _ -> return None
                  in
                  match name with
                  | Some name ->
                      let* error_handler = of_expression typ_vars c_rhs in
                      error_message
                        (Apply
                           ( Variable
                               ( MixedPath.of_name
                                   (Name.of_string_raw "try_with"),
                                 [] ),
                             [
                               Some (Function (Name.Nameless, None, e));
                               Some (Function (name, None, error_handler));
                             ] ))
                        SideEffect
                        ("Try-with are not handled\n\n"
                       ^ "Alternative: use sum types (\"option\", \"result\", \
                          ...) to represent an error case.")
                  | None -> default_error)
              | _ -> default_error)
          | Texp_setfield (e_record, _, { lbl_name; _ }, e) ->
              of_expression typ_vars e_record >>= fun e_record ->
              of_expression typ_vars e >>= fun e ->
              error_message
                (Apply
                   ( Error "set_record_field",
                     [
                       Some e_record;
                       Some (Constant (Constant.String lbl_name));
                       Some e;
                     ] ))
                SideEffect "Set record field not handled."
          | Texp_array es ->
              Monad.List.map (of_expression typ_vars) es >>= fun es ->
              error_message (ErrorArray es) NotSupported "Arrays not handled."
          | Texp_while _ ->
              error_message (Error "while") SideEffect
                "While loops not handled."
          | Texp_for _ ->
              error_message (Error "for") SideEffect "For loops not handled."
          | Texp_send _ ->
              error_message (Error "send") NotSupported
                "Sending method message is not handled"
          | Texp_new _ ->
              error_message (Error "new") NotSupported
                "Creation of new objects is not handled"
          | Texp_instvar _ ->
              error_message (Error "instance_variable") NotSupported
                "Creating an instance variable is not handled"
          | Texp_setinstvar _ ->
              error_message (Error "set_instance_variable") SideEffect
                "Setting an instance variable is not handled"
          | Texp_override _ ->
              error_message (Error "override") NotSupported
                "Overriding is not handled"
          | Texp_letmodule
              ( x,
                _,
                _,
                {
                  mod_desc =
                    Tmod_unpack ({ exp_desc = Texp_ident (path, _, _); _ }, _);
                  _;
                },
                e ) ->
              let* x = Name.of_optional_ident true x in
              PathName.of_path_with_convert false path >>= fun path_name ->
              of_expression typ_vars e >>= fun e ->
              return (LetModuleUnpack (x, path_name, e))
          | Texp_letmodule (x, _, _, module_expr, e) ->
              let* x = Name.of_optional_ident true x in
              push_env
                ( of_module_expr typ_vars module_expr None >>= fun value ->
                  set_env e.exp_env
                    (push_env
                       ( of_expression typ_vars e >>= fun e ->
                         return (LetVar (None, x, [], value, e)) )) )
          | Texp_letexception _ ->
              error_message (Error "let_exception") SideEffect
                "Let of exception is not handled"
          | Texp_assert e' ->
              Type.of_typ_expr false typ_vars e.exp_type >>= fun (typ, _, _) ->
              of_expression typ_vars e' >>= fun e' ->
              error_message
                (Assert (typ, e'))
                SideEffect "Assert instruction is not handled."
          | Texp_lazy e ->
              of_expression typ_vars e >>= fun e ->
              error_message
                (Apply (Error "lazy", [ Some e ]))
                SideEffect "Lazy expressions are not handled"
          | Texp_object _ ->
              error_message (Error "object") NotSupported
                "Creation of objects is not handled"
          | Texp_pack module_expr ->
              let* module_typ_params =
                ModuleTypParams.get_module_typ_typ_params_arity
                  module_expr.mod_type
              in
              push_env (of_module_expr typ_vars module_expr None) >>= fun e ->
              return (ModulePack (module_typ_params, e))
          | Texp_letop
              {
                let_ = { bop_op_path; bop_exp; _ };
                ands;
                body = { c_lhs; c_rhs; _ };
                _;
              } -> (
              match ands with
              | [] -> (
                  let* let_symbol_mixed_path =
                    MixedPath.of_path true bop_op_path
                  in
                  let let_symbol = MixedPath.to_string let_symbol_mixed_path in
                  let* configuration = get_configuration in
                  let let_symbol =
                    Configuration.is_monadic_let configuration let_symbol
                  in
                  let* pattern = Pattern.of_pattern c_lhs in
                  let* e1 = of_expression typ_vars bop_exp in
                  let* e2 = of_expression typ_vars c_rhs in
                  let cases =
                    match pattern with
                    | None -> []
                    | Some pattern -> [ (pattern, None, e2) ]
                  in
                  match (let_symbol, pattern) with
                  | None, Some (Variable name) ->
                      return
                        (Apply
                           ( Variable (let_symbol_mixed_path, []),
                             [ Some e1; Some (Function (name, None, e2)) ] ))
                  | None, _ ->
                      return
                        (Apply
                           ( Variable (let_symbol_mixed_path, []),
                             [
                               Some e1;
                               Some
                                 (Function
                                    ( Name.FunctionParameter,
                                      None,
                                      Match
                                        ( Variable
                                            ( MixedPath.PathName
                                                {
                                                  PathName.path = [];
                                                  base = Name.FunctionParameter;
                                                },
                                              [] ),
                                          None,
                                          cases,
                                          false ) ));
                             ] ))
                  | Some let_symbol, Some (Variable name) ->
                      return (LetVar (Some let_symbol, name, [], e1, e2))
                  | Some let_symbol, _ ->
                      return
                        (LetVar
                           ( Some let_symbol,
                             Name.FunctionParameter,
                             [],
                             e1,
                             Match
                               ( Variable
                                   ( MixedPath.PathName
                                       {
                                         PathName.path = [];
                                         base = Name.FunctionParameter;
                                       },
                                     [] ),
                                 None,
                                 cases,
                                 false ) )))
              | _ :: _ ->
                  error_message (Error "let_op_and") NotSupported
                    "We do not support let operators with and")
          | Texp_unreachable ->
              error_message (Error "unreachable") NotSupported
                "Unreachable expressions are not supported"
          | Texp_extension_constructor _ ->
              error_message (Error "extension") NotSupported
                "Construction of extensions is not handled"
          | Texp_open (_, e) -> of_expression typ_vars e
          | Texp_hole ->
              error_message (Error "expression_hole") Unexpected
                "Unexpected expression hole"
        in
        if Attribute.has_cast attributes then
          let* typ, _, _ = Type.of_typ_expr false typ_vars typ in
          return (Cast (e, typ))
        else if Attribute.has_typ_annotation attributes then
          let* typ, _, _ = Type.of_typ_expr false typ_vars typ in
          return (TypAnnotation (e, typ))
        else return e))

and of_match :
    type k.
    Name.t Name.Map.t ->
    t ->
    k case list ->
    bool ->
    bool ->
    bool ->
    bool ->
    bool ->
    t Monad.t =
 fun typ_vars e cases is_gadt_match is_tagged_match do_cast_results
     is_with_default_case is_grab_existentials ->
  let is_extensible_type_match =
    cases
    |> List.map (fun { c_lhs; _ } -> c_lhs)
    |> Pattern.are_extensible_patterns_or_any true
  in
  if is_extensible_type_match then of_match_extensible typ_vars e cases
  else
    let* (dep_match : dependent_pattern_match option) =
      match cases with
      | [] -> return None
      | { c_lhs; c_rhs; _ } :: _ ->
          if not is_tagged_match then return None
          else
            let* cast, _, new_typ_vars =
              Type.of_typ_expr true Name.Map.empty c_lhs.pat_type
            in
            let* motive, _, new_typ_vars' =
              Type.of_typ_expr true Name.Map.empty c_rhs.exp_type
            in
            let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
            let* cast = Type.decode_var_tags new_typ_vars false cast in
            let* motive = Type.decode_var_tags new_typ_vars false motive in
            let cast, args = Type.normalize_constructor cast in
            (* Only generates dependent pattern matching for actual gadts *)
            if List.length args = 0 || Type.is_native_type cast then return None
            else return (Some { cast; args; motive })
    in
    cases
    |> Monad.List.filter_map (fun { c_lhs; c_guard; c_rhs } ->
           set_loc c_lhs.pat_loc
             (let* bound_vars =
                Typedtree.pat_bound_idents c_lhs
                |> List.rev
                |> Monad.List.map (fun ident ->
                       let { Types.val_type; _ } =
                         Env.find_value (Path.Pident ident) c_rhs.exp_env
                       in
                       let* name = Name.of_ident true ident in
                       return (name, val_type))
              in
              let typs = List.map snd bound_vars in
              let tag_list = Type.tag_no_args typs in
              let* new_typ_vars =
                Type.typed_existential_typs_of_typs typs tag_list
              in
              Monad.List.map
                (fun (name, typ) ->
                  Type.of_typ_expr true typ_vars typ >>= fun (typ, _, _) ->
                  return (name, typ))
                bound_vars
              >>= fun bound_vars ->
              let env_has_tag =
                List.exists (fun (_, ki) -> ki = Kind.Tag) new_typ_vars
              in
              let new_typ_vars =
                if is_gadt_match then new_typ_vars
                else
                  let free_vars =
                    Type.local_typ_constructors_of_typs
                      (List.map snd bound_vars)
                    |> Name.Set.elements
                  in
                  let tag_vars =
                    new_typ_vars
                    |> List.filter_map (fun (name, ki) ->
                           if ki = Kind.Tag then Some name else None)
                  in
                  VarEnv.keep_only (free_vars @ tag_vars) new_typ_vars
              in

              let* bound_vars =
                Monad.List.map
                  (fun (x, ty) ->
                    let* ty = Type.decode_var_tags new_typ_vars false ty in
                    return (x, ty))
                  bound_vars
              in

              let* typ =
                if is_gadt_match || do_cast_results || not env_has_tag then
                  let* typ, _, _ =
                    Type.of_typ_expr true typ_vars c_rhs.exp_type
                  in
                  return typ
                else
                  (* Only expand type if you really need to. It may cause the translation to break *)
                  let typ =
                    Ctype.full_expand ~may_forget_scope:false c_rhs.exp_env
                      c_rhs.exp_type
                  in
                  let* typ, _, _ = Type.of_typ_expr true typ_vars typ in
                  return typ
              in

              let existential_cast =
                Some
                  {
                    new_typ_vars;
                    bound_vars;
                    return_typ = typ;
                    use_axioms = is_gadt_match;
                    cast_result = do_cast_results;
                    enable = is_grab_existentials || is_gadt_match;
                  }
              in

              (match c_guard with
              | Some guard ->
                  of_expression typ_vars guard >>= fun guard ->
                  return (Some guard)
              | None -> return None)
              >>= fun guard ->
              Pattern.of_pattern c_lhs >>= fun pattern ->
              match c_rhs.exp_desc with
              | Texp_unreachable -> return None
              | _ ->
                  of_expression typ_vars c_rhs >>= fun e ->
                  let e = dependent_transform e dep_match in
                  return
                    (pattern
                    |> Option.map (fun pattern ->
                           (pattern, existential_cast, guard, e)))))
    >>= fun cases_with_guards ->
    let guards =
      cases_with_guards
      |> List.filter_map (function
           | p, _, Some guard, _ -> Some (p, guard)
           | _ -> None)
    in
    let guard_checks =
      guards
      |> List.map (fun (p, guard) ->
             let is_pattern_always_true =
               match p with
               | Pattern.Any | Pattern.Variable _ -> true
               | _ -> false
             in
             let cases =
               [ (p, None, guard) ]
               @
               if is_pattern_always_true then []
               else
                 [
                   ( Pattern.Any,
                     None,
                     Variable (MixedPath.PathName PathName.false_value, []) );
                 ]
             in
             Match (e, None, cases, false))
    in
    let e = match guards with [] -> e | _ :: _ -> Tuple (e :: guard_checks) in
    let i = ref (-1) in
    let nb_guards = List.length guard_checks in
    let cases =
      cases_with_guards
      |> List.map (fun (p, existential_cast, guard, rhs) ->
             let is_guarded =
               match guard with Some _ -> true | None -> false
             in
             if is_guarded then i := !i + 1;
             let p =
               if nb_guards = 0 then p
               else
                 Pattern.Tuple
                   (p :: any_patterns_with_ith_true is_guarded !i nb_guards)
             in
             (p, existential_cast, rhs))
    in
    (* We remove unused existential type variables *)
    let cases =
      cases
      |> List.map (fun (p, existential_cast, rhs) ->
             let existential_cast =
               match existential_cast with
               | None -> None
               | Some existential_cast ->
                   let { new_typ_vars; bound_vars; return_typ; _ } =
                     existential_cast
                   in
                   let free_typ_vars =
                     let typs = return_typ :: List.map snd bound_vars in
                     Name.Set.union
                       (Type.local_typ_constructors_of_typs typs)
                       (free_existential_typs rhs)
                   in
                   Some
                     {
                       existential_cast with
                       new_typ_vars =
                         VarEnv.keep_only
                           (Name.Set.elements free_typ_vars)
                           new_typ_vars;
                     }
             in
             (p, existential_cast, rhs))
    in
    let t = Match (e, dep_match, cases, is_with_default_case) in
    (* If its a deppendent pattern matching then add eq_refl at the end of the match *)
    match dep_match with
    | None -> return t
    | Some dep_match ->
        let eq_refl = "eq_refl" |> Name.of_string_raw |> MixedPath.of_name in
        let ts =
          List.map (fun _ -> Some (Variable (eq_refl, []))) dep_match.args
        in
        return (Apply (t, ts))

(** We suppose that we know that we have a match of extensible types. *)
and of_match_extensible :
    type kind. Name.t Name.Map.t -> t -> kind case list -> t Monad.t =
 fun (typ_vars : Name.t Name.Map.t) (e : t) (cases : kind case list) ->
  let* cases =
    cases
    |> Monad.List.map (fun { c_lhs; c_rhs; _ } ->
           set_loc c_lhs.pat_loc
             (let* p = Pattern.of_extensible_pattern c_lhs in
              let* e = of_expression typ_vars c_rhs in
              return (p, e)))
  in
  return (MatchExtensible (e, cases))

(** Generate a variable and a "match" on this variable from a list of
    patterns. *)
and open_cases (type pattern_kind) (typ_vars : Name.t Name.Map.t)
    (cases : pattern_kind case list) (is_gadt_match : bool)
    (is_tagged_match : bool) (do_cast_results : bool)
    (is_with_default_case : bool) (is_grab_existentials : bool) :
    (Name.t * Type.t option * t) Monad.t =
  let name = Name.FunctionParameter in
  let* typ =
    match cases with
    | [] -> return None
    | { c_lhs = { pat_type; _ }; _ } :: _ ->
        let* typ, _, _ = Type.of_typ_expr true typ_vars pat_type in
        return (Some typ)
  in
  let e = Variable (MixedPath.of_name name, []) in
  let* e =
    of_match typ_vars e cases is_gadt_match is_tagged_match do_cast_results
      is_with_default_case is_grab_existentials
  in
  return (name, typ, e)

and import_let_fun (typ_vars : Name.t Name.Map.t) (at_top_level : bool)
    (is_rec : Asttypes.rec_flag) (cases : value_binding list) :
    t option Definition.t Monad.t =
  let is_rec = Recursivity.of_rec_flag is_rec in
  cases
  |> Monad.List.filter_map (fun { vb_pat = p; vb_expr; vb_attributes; _ } ->
         Attribute.of_attributes vb_attributes >>= fun attributes ->
         let is_axiom = Attribute.has_axiom_with_reason attributes in
         let structs = Attribute.get_structs attributes in
         let* _ =
           match structs with [] -> return () | _ :: _ -> use_unsafe_fixpoint
         in
         set_env vb_expr.exp_env
           (set_loc p.pat_loc
              ( Pattern.of_pattern p >>= fun p ->
                (match p with
                | Some Pattern.Any -> return None
                | Some (Pattern.Variable x) -> return (Some x)
                | _ ->
                    raise None Unexpected
                      "A variable name instead of a pattern was expected")
                >>= fun x ->
                let predefined_variables =
                  List.map snd (Name.Map.bindings typ_vars)
                in
                let exp_type =
                  (* Special case for functions whose type is given by a type
                     synonym at the end rather than with a type on each
                     parameter or an explicit arrow type. *)
                  match (vb_expr.exp_desc, vb_expr.exp_type.desc) with
                  | Texp_function _, Tconstr (path, _, _) -> (
                      match Env.find_type path vb_expr.exp_env with
                      | { type_manifest = Some ty; _ } -> ty
                      | _ | (exception _) -> vb_expr.exp_type)
                  | _ -> vb_expr.exp_type
                in
                Type.of_typ_expr true typ_vars exp_type
                >>= fun (e_typ, typ_vars, new_typ_vars) ->
                let* e_typ = Type.decode_var_tags new_typ_vars false e_typ in
                let new_typ_vars =
                  VarEnv.remove predefined_variables new_typ_vars
                in
                match x with
                | None -> return None
                | Some x ->
                    let* args_names, e_body =
                      if not is_axiom then
                        let* e = of_expression typ_vars vb_expr in
                        let args_names, e_body = open_function e in
                        return (args_names, Some e_body)
                      else return ([], None)
                    in
                    let* args_typs, e_body_typ =
                      Type.open_type e_typ (List.length args_names)
                    in
                    let header =
                      {
                        Header.name = x;
                        typ_vars = new_typ_vars;
                        args = List.combine args_names args_typs;
                        structs;
                        typ = e_body_typ;
                        is_notation =
                          Attribute.has_mutual_as_notation attributes;
                      }
                    in
                    return (Some (header, e_body)) )))
  >>= fun cases ->
  let result = { Definition.is_rec; cases } in
  match (at_top_level, result) with
  | false, { is_rec = true; cases = _ :: _ :: _ } ->
      raise result NotSupported
        "Mutually recursive definition are only handled at top-level"
  | _ -> return result

and of_let (typ_vars : Name.t Name.Map.t) (is_rec : Asttypes.rec_flag)
    (cases : Typedtree.value_binding list) (e2 : t) : t Monad.t =
  match cases with
  | [
   {
     vb_pat =
       {
         pat_desc =
           Tpat_construct
             (_, { cstr_res = { desc = Tconstr (path, _, _); _ }; _ }, _, _);
         _;
       };
     _;
   };
  ]
    when PathName.is_unit path ->
      raise
        (ErrorMessage (e2, "top_level_evaluation"))
        SideEffect "Top-level evaluations are ignored"
  | _ -> (
      (match cases with
      | [ { vb_expr = { exp_desc; exp_type; _ }; _ } ]
        when match exp_desc with Texp_function _ -> false | _ -> true ->
          Type.of_typ_expr true typ_vars exp_type >>= fun (_, typ_vars', _) ->
          let typ_vars = List.map fst (Name.Map.bindings typ_vars) in
          let new_vars =
            List.fold_left
              (fun map var -> Name.Map.remove var map)
              typ_vars' typ_vars
          in
          return (not @@ Name.Map.is_empty new_vars)
      | _ -> return true)
      >>= fun is_function ->
      match cases with
      | [ { vb_pat = p; vb_expr = e1; vb_attributes; _ } ] when not is_function
        -> (
          let* attributes = Attribute.of_attributes vb_attributes in
          let has_tagged_match = Attribute.has_tagged_match attributes in
          let* p_typ = Type.of_type_expr_without_free_vars p.pat_type in
          let* p = Pattern.of_pattern p in
          let* e1_typ = Type.of_type_expr_without_free_vars e1.exp_type in
          let* e1 = of_expression typ_vars e1 in
          let dep_match =
            if has_tagged_match then
              Some { cast = p_typ; args = []; motive = e1_typ }
            else None
          in
          match p with
          | Some (Pattern.Variable x) -> return (LetVar (None, x, [], e1, e2))
          | Some p ->
              let is_with_default_case =
                Attribute.has_match_with_default attributes
              in
              return
                (Match (e1, dep_match, [ (p, None, e2) ], is_with_default_case))
          | None -> return (Match (e1, dep_match, [], false)))
      | _ ->
          import_let_fun typ_vars false is_rec cases >>= fun def ->
          return (LetFun (def, e2)))

and of_module_expr (typ_vars : Name.t Name.Map.t)
    (module_expr : Typedtree.module_expr)
    (module_type : Types.module_type option) : t Monad.t =
  let { mod_desc; mod_env; mod_loc; mod_type = local_module_type; _ } =
    module_expr
  in
  set_env mod_env
    (set_loc mod_loc
       (let* is_local_module_typ_first_class =
          let path =
            match mod_desc with Tmod_ident (path, _) -> Some path | _ -> None
          in
          IsFirstClassModule.is_module_typ_first_class local_module_type path
        in
        let* is_module_typ_first_class =
          match module_type with
          | None -> return None
          | Some module_type ->
              let* is_first_class =
                IsFirstClassModule.is_module_typ_first_class module_type None
              in
              return (Some (is_first_class, module_type))
        in
        (* We consider casts to a first-class module of a different kind, either from
           another first-class module or from a plain module. *)
        let get_is_cast_needed module_type_path =
          match is_local_module_typ_first_class with
          | Found local_module_type_path ->
              let* comparison =
                PathName.compare_paths local_module_type_path module_type_path
              in
              return (comparison <> 0)
          | _ -> return true
        in
        let cast_path path module_type module_type_path =
          let* values = ModuleTypValues.get typ_vars module_type in
          let* module_typ_params_arity =
            ModuleTypParams.get_module_typ_typ_params_arity module_type
          in
          let mixed_path_of_value_or_typ (name : Name.t) : MixedPath.t Monad.t =
            match is_local_module_typ_first_class with
            | Found local_module_type_path ->
                let* base = PathName.of_path_with_convert false path in
                let* field =
                  PathName.of_path_and_name_with_convert local_module_type_path
                    name
                in
                return (MixedPath.Access (base, [ field ]))
            | _ ->
                let* path_name =
                  PathName.of_path_and_name_with_convert path name
                in
                return (MixedPath.PathName path_name)
          in
          build_module module_typ_params_arity values module_type_path
            mixed_path_of_value_or_typ
        in
        match mod_desc with
        | Tmod_ident (path, _) -> (
            let* mixed_path = MixedPath.of_path false path in
            let default_result = return (Variable (mixed_path, [])) in
            match is_module_typ_first_class with
            | Some (Found module_type_path, module_type) ->
                let* is_cast_needed = get_is_cast_needed module_type_path in
                if not is_cast_needed then default_result
                else cast_path path module_type module_type_path
            | _ -> default_result)
        | Tmod_structure structure -> (
            match is_module_typ_first_class with
            | Some (Found signature_path, module_type) ->
                of_structure typ_vars signature_path module_type
                  structure.str_items structure.str_final_env
            | Some (IsFirstClassModule.Not_found reason, _) ->
                error_message
                  (Error "first_class_module_value_of_unknown_signature") Module
                  ("The signature name of this module could not be found\n\n"
                 ^ reason)
            | None ->
                error_message (Error "no_expected_module_type_found") Unexpected
                  ("No module type was found for this structure.\n"
                 ^ "Try to add a module type annotation."))
        | Tmod_functor (parameter, e) -> (
            let* e = of_module_expr typ_vars e None in
            match parameter with
            | Named (ident, _, module_typ_arg) ->
                let* x = Name.of_optional_ident false ident in
                let id = Name.string_of_optional_ident ident in
                let* module_typ_arg = ModuleTyp.of_ocaml module_typ_arg in
                let* _, module_typ_arg =
                  ModuleTyp.to_typ [] id false module_typ_arg
                in
                return (Functor (x, module_typ_arg, e))
            | Unit -> return e)
        | Tmod_apply (e1, e2, _) -> (
            let e1_mod_type = e1.mod_type in
            let expected_module_typ_for_e2 =
              match e1_mod_type with
              | Mty_functor (Named (_, module_typ_arg), _) ->
                  Some module_typ_arg
              | _ -> None
            in
            let* e1 = of_module_expr typ_vars e1 None in
            let* es =
              match e1_mod_type with
              | Mty_functor (Unit, _) -> return []
              | _ ->
                  let* e2 =
                    of_module_expr typ_vars e2 expected_module_typ_for_e2
                  in
                  return [ Some e2 ]
            in
            let application = Apply (e1, es) in
            match is_module_typ_first_class with
            | Some (Found module_type_path, module_type) ->
                let* is_cast_needed = get_is_cast_needed module_type_path in
                if not is_cast_needed then return application
                else
                  let ident = Ident.create_local "functor_result" in
                  let* name = Name.of_ident false ident in
                  let path = Path.Pident ident in
                  let* casted_result =
                    cast_path path module_type module_type_path
                  in
                  return (LetVar (None, name, [], application, casted_result))
            | _ -> return application)
        | Tmod_constraint (module_expr, mod_type, _, _) ->
            let module_type =
              match module_type with
              | Some _ -> module_type
              | None -> Some mod_type
            in
            of_module_expr typ_vars module_expr module_type
        | Tmod_unpack (e, _) ->
            of_expression typ_vars e >>= fun e ->
            raise e Module
              ("We do not support unpacking of first-class module outside of "
             ^ "expressions.\n\n"
             ^ "This is to prevent universe inconsistencies in Coq. A module \
                can " ^ "become first-class but not the other way around.")
        | Tmod_hole ->
            raise (Error "module_hole") Unexpected "Unexpected module hole."))

and of_structure (typ_vars : Name.t Name.Map.t) (signature_path : Path.t)
    (module_type : Types.module_type) (items : Typedtree.structure_item list)
    (final_env : Env.t) : t Monad.t =
  match items with
  | [] ->
      set_env final_env
        ( ModuleTypParams.get_module_typ_typ_params_arity module_type
        >>= fun module_typ_params_arity ->
          let* values = ModuleTypValues.get typ_vars module_type in
          let mixed_path_of_value_or_typ (name : Name.t) : MixedPath.t Monad.t =
            return (MixedPath.of_name name)
          in
          build_module module_typ_params_arity values signature_path
            mixed_path_of_value_or_typ )
  | item :: items ->
      set_env item.str_env
        (set_loc item.str_loc
           ( of_structure typ_vars signature_path module_type items final_env
           >>= fun e_next ->
             match item.str_desc with
             | Tstr_eval _ ->
                 raise
                   (ErrorMessage (e_next, "top_level_evaluation"))
                   SideEffect "Top-level evaluations are ignored"
             | Tstr_value (rec_flag, cases) ->
                 push_env (of_let typ_vars rec_flag cases e_next)
             | Tstr_primitive _ ->
                 raise
                   (ErrorMessage (e_next, "primitive"))
                   NotSupported "Primitive not handled"
             | Tstr_type (_, typs) -> (
                 match typs with
                 | [ typ ] -> (
                     match typ with
                     | {
                      typ_id;
                      typ_type =
                        {
                          type_kind = Type_abstract;
                          type_manifest = Some typ;
                          type_params;
                          _;
                        };
                      _;
                     } ->
                         let* name = Name.of_ident false typ_id in
                         type_params
                         |> Monad.List.map Type.of_type_expr_variable
                         >>= fun typ_args ->
                         Type.of_type_expr_without_free_vars typ >>= fun typ ->
                         return (LetTyp (name, typ_args, typ, e_next))
                     | _ ->
                         raise
                           (ErrorMessage (e_next, "typ_definition"))
                           NotSupported
                           ("We only handle type synonyms here." ^ "\n\n"
                          ^ "Indeed, we compile this module as a dependent \
                             record for " ^ "the signature:\n"
                          ^ Path.name signature_path ^ "\n\n"
                          ^ "Thus we cannot introduce new type definitions. \
                             Use a "
                          ^ "separated module for the type definition and\n\
                             its use."))
                 | _ ->
                     raise
                       (ErrorMessage (e_next, "mutual_typ_definition"))
                       NotSupported
                       "Mutually recursive type definition not handled here")
             | Tstr_typext _ -> return e_next
             | Tstr_exception _ -> return e_next
             | Tstr_module { mb_id = Some ident; _ }
               when Ident.name ident = "Internal_for_tests" ->
                 return e_next
             | Tstr_module { mb_id; mb_expr; _ } ->
                 let* name = Name.of_optional_ident false mb_id in
                 of_module_expr typ_vars mb_expr (Some mb_expr.mod_type)
                 >>= fun value ->
                 return (LetVar (None, name, [], value, e_next))
             | Tstr_recmodule _ ->
                 raise
                   (ErrorMessage (e_next, "recursive_module"))
                   NotSupported "Recursive modules not handled"
             | Tstr_modtype _ ->
                 raise
                   (ErrorMessage (e_next, "module_type"))
                   NotSupported
                   "Module type not handled in module with a named signature"
             | Tstr_open _ ->
                 raise
                   (ErrorMessage (e_next, "open"))
                   NotSupported
                   "Open not handled in module with a named signature"
             | Tstr_class _ ->
                 raise
                   (ErrorMessage (e_next, "class"))
                   NotSupported "Class not handled"
             | Tstr_class_type _ ->
                 raise
                   (ErrorMessage (e_next, "class_type"))
                   NotSupported "Class type not handled"
             | Tstr_include { incl_mod; incl_type; _ } -> (
                 let path =
                   match incl_mod.mod_desc with
                   | Tmod_ident (path, _)
                   | Tmod_constraint
                       ({ mod_desc = Tmod_ident (path, _); _ }, _, _, _) ->
                       Some path
                   | _ -> None
                 in
                 let incl_module_type = Types.Mty_signature incl_type in
                 let* is_first_class =
                   IsFirstClassModule.is_module_typ_first_class incl_module_type
                     path
                 in
                 match is_first_class with
                 | Found incl_signature_path -> (
                     match path with
                     | Some path ->
                         let* path_name =
                           PathName.of_path_with_convert false path
                         in
                         of_include typ_vars path_name incl_signature_path
                           incl_type e_next
                     | None ->
                         let* name = get_include_name incl_mod in
                         let path_name = PathName.of_name [] name in
                         let* included_module =
                           of_module_expr typ_vars incl_mod
                             (Some incl_module_type)
                         in
                         let* e_next =
                           of_include typ_vars path_name incl_signature_path
                             incl_type e_next
                         in
                         return
                           (LetVar (None, name, [], included_module, e_next)))
                 | Not_found reason ->
                     raise
                       (ErrorMessage (e_next, "include_without_named_signature"))
                       NotSupported
                       ("We did not find a signature name for the include of \
                         this module\n\n" ^ reason))
             | Tstr_attribute _ -> return e_next ))

and of_include (typ_vars : Name.t Name.Map.t) (module_path_name : PathName.t)
    (signature_path : Path.t) (signature : Types.signature) (e_next : t) :
    t Monad.t =
  match signature with
  | [] -> return e_next
  | signature_item :: signature -> (
      of_include typ_vars module_path_name signature_path signature e_next
      >>= fun e_next ->
      match signature_item with
      | Sig_value (ident, _, _) | Sig_type (ident, _, _, _) ->
          let is_value =
            match signature_item with Sig_value _ -> true | _ -> false
          in
          (match signature_item with
          | Sig_value (_, { Types.val_type; _ }, _) ->
              Type.of_typ_expr true typ_vars val_type
              >>= fun (_, _, new_typ_vars) -> return (List.map fst new_typ_vars)
          | _ -> return [])
          >>= fun typ_vars ->
          let* name = Name.of_ident is_value ident in
          PathName.of_path_and_name_with_convert signature_path name
          >>= fun signature_path_name ->
          return
            (LetVar
               ( None,
                 name,
                 typ_vars,
                 Variable
                   ( MixedPath.Access (module_path_name, [ signature_path_name ]),
                     [] ),
                 e_next ))
      | Sig_typext _ | Sig_module _ | Sig_modtype _ | Sig_class _
      | Sig_class_type _ ->
          return e_next)

let rec flatten_list (e : t) : t list option =
  match e with
  | Constructor (x, _, es) -> (
      match (x, es) with
      | { PathName.path = []; base = Name.Make "[]" }, [] -> Some []
      | { PathName.path = []; base = Name.Make "cons" }, [ e; es ] -> (
          match flatten_list es with Some es -> Some (e :: es) | None -> None)
      | _ -> None)
  | _ -> None

let to_coq_let_symbol (let_symbol : string option) : SmartPrint.t =
  match let_symbol with None -> !^"let" | Some let_symbol -> !^let_symbol

let to_coq_implicit (implicit : string * string) : SmartPrint.t =
  let name, value = implicit in
  nest (parens (!^name ^^ !^":=" ^^ !^value))

(** Pretty-print an expression to Coq (inside parenthesis if the [paren] flag is
    set). *)
let rec to_coq (paren : bool) (e : t) : SmartPrint.t =
  match e with
  | Constant c -> Constant.to_coq c
  | Variable (x, implicits) -> (
      let x = MixedPath.to_coq x in
      match implicits with
      | [] -> x
      | _ :: _ ->
          parens (separate space (x :: List.map to_coq_implicit implicits)))
  | Tuple es -> (
      match es with
      | [] -> !^"tt"
      | [ e ] -> to_coq paren e
      | _ :: _ :: _ ->
          parens @@ nest
          @@ separate (!^"," ^^ space) (List.map (to_coq true) es))
  | Constructor (x, implicits, es) -> (
      let implicits = List.map to_coq_implicit implicits in
      match flatten_list e with
      | Some [] -> (
          let nil = !^"nil" in
          match implicits with
          | [] -> nil
          | _ :: _ -> parens (separate space (nil :: implicits)))
      | Some es -> OCaml.list (to_coq false) es
      | None -> (
          let arguments = implicits @ List.map (to_coq true) es in
          match arguments with
          | [] -> PathName.to_coq x
          | _ :: _ ->
              Pp.parens paren @@ nest
              @@ separate space (PathName.to_coq x :: arguments)))
  | ConstructorExtensible (tag, typ, payload) ->
      Pp.parens paren
        (nest
           (!^"Build_extensible"
           ^^ !^("\"" ^ tag ^ "\"")
           ^^ Type.to_coq None (Some Type.Context.Apply) typ
           ^^ to_coq true payload))
  | ConstructorVariant (tag, typ_payload) ->
      Pp.parens paren
        (nest
           (!^"Variant.Build"
           ^^ !^("\"" ^ tag ^ "\"")
           ^^ (match typ_payload with
              | None -> !^"unit"
              | Some (typ, _) -> Type.to_coq None (Some Type.Context.Apply) typ)
           ^^
           match typ_payload with
           | None -> !^"tt"
           | Some (_, payload) -> to_coq true payload))
  | Apply (e_f, e_xs) -> (
      match e_f with
      | Apply (e_f, e_xs')
        when List.for_all (function None -> false | Some _ -> true) e_xs' ->
          to_coq paren (Apply (e_f, e_xs' @ e_xs))
      | _ ->
          let missing_args, all_args, _ =
            List.fold_left
              (fun (missing_args, all_args, index) e_x ->
                match e_x with
                | None ->
                    let missing_arg = !^("x_" ^ string_of_int index) in
                    ( missing_args @ [ missing_arg ],
                      all_args @ [ missing_arg ],
                      index + 1 )
                | Some e_x ->
                    (missing_args, all_args @ [ to_coq true e_x ], index))
              ([], [], 1) e_xs
          in
          Pp.parens paren
            (nest
               ((match missing_args with
                | [] -> empty
                | _ :: _ ->
                    !^"fun" ^^ separate space missing_args ^^ !^"=>" ^^ space)
               ^-^ nest (separate space (to_coq true e_f :: all_args)))))
  | Return ("", e) -> to_coq paren e
  | Return (operator, e) ->
      Pp.parens paren @@ nest @@ !^operator ^^ to_coq true e
  | InfixOperator (operator, e1, e2) ->
      Pp.parens paren @@ group @@ to_coq true e1 ^^ !^operator ^^ to_coq true e2
  | Function (x, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ (match typ with
              | None -> Name.to_coq x
              | Some typ ->
                  parens (Name.to_coq x ^^ !^":" ^^ Type.to_coq None None typ))
           ^^ !^"=>" ^^ to_coq false e)
  | Functions (xs, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ separate space (List.map Name.to_coq xs)
           ^^ !^"=>" ^^ to_coq false e)
  | LetVar (let_symbol, x, typ_params, e1, e2) -> (
      let get_default () =
        Pp.parens paren
        @@ nest
             (to_coq_let_symbol let_symbol
             ^^ Name.to_coq x
             ^^ (match typ_params with
                | [] -> empty
                | _ :: _ ->
                    braces
                      (nest
                         (separate space (typ_params |> List.map Name.to_coq)
                         ^^ !^":" ^^ !^"Set")))
             ^^ !^":=" ^^ to_coq false e1 ^^ !^"in" ^^ newline
             ^^ to_coq false e2)
      in
      match (let_symbol, x, e1, e2) with
      | None, _, Variable (PathName { path = []; base }, []), _
        when Name.equal base x ->
          to_coq paren e2
      | ( _,
          Name.FunctionParameter,
          _,
          Match
            ( Variable
                ( MixedPath.PathName
                    { PathName.path = []; base = Name.FunctionParameter },
                  [] ),
              _,
              cases,
              is_with_default_case ) ) -> (
          let single_let =
            to_coq_try_single_let_pattern paren let_symbol e1 cases
              is_with_default_case
          in
          match single_let with
          | Some single_let -> single_let
          | None -> get_default ())
      | _ -> get_default ())
  | LetFun (def, e) ->
      (* There should be only one case for recursive definitionss. *)
      Pp.parens paren
      @@ nest
           (separate newline
              (def.Definition.cases
              |> List.mapi (fun index (header, e) ->
                     let first_case = index = 0 in
                     (if first_case then
                      !^"let"
                      ^^ if def.Definition.is_rec then !^"fix" else empty
                     else if def.Definition.is_rec then !^"with"
                     else !^"in" ^^ !^"let")
                     ^^ Name.to_coq header.Header.name
                     ^^ Type.typ_vars_to_coq braces empty empty
                          header.Header.typ_vars
                     ^^ group
                          (separate space
                             (header.Header.args
                             |> List.map (fun (x, x_typ) ->
                                    parens
                                      (nest
                                         (Name.to_coq x ^^ !^":"
                                         ^^ Type.to_coq None None x_typ)))))
                     ^^ Header.to_coq_structs header
                     ^^ !^": "
                     ^-^ Type.to_coq None None header.Header.typ
                     ^-^ !^" :=" ^^ newline
                     ^^ indent
                          (match e with
                          | None -> !^"axiom"
                          | Some e -> to_coq false e)))
           ^^ !^"in" ^^ newline ^^ to_coq false e)
  | LetTyp (x, typ_args, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"let" ^^ Name.to_coq x
           ^^ (match typ_args with
              | [] -> empty
              | _ ->
                  parens
                    (separate space (List.map Name.to_coq typ_args)
                    ^^ !^":" ^^ Pp.set))
           ^^ !^":" ^^ Pp.set ^^ !^":=" ^^ Type.to_coq None None typ ^^ !^"in"
           ^^ newline ^^ to_coq false e)
  | LetModuleUnpack (x, path_name, e2) ->
      Pp.parens paren
      @@ nest
           (!^"let" ^^ !^"'existS" ^^ !^"_" ^^ !^"_" ^^ Name.to_coq x ^^ !^":="
          ^^ PathName.to_coq path_name ^^ !^"in" ^^ newline ^^ to_coq false e2)
  | Match (e, dep_match, cases, is_with_default_case) -> (
      let single_let =
        to_coq_try_single_let_pattern paren None e cases is_with_default_case
      in
      match single_let with
      | Some single_let -> single_let
      | None ->
          let dep_match_print =
            match dep_match with
            | None -> empty
            | Some { cast; args; motive } ->
                !^"in" ^^ Type.to_coq None None cast ^^ !^"return"
                ^^ separate
                     (space ^^ !^"->" ^^ space)
                     (List.map (Type.to_coq None None) (args @ [ motive ]))
          in
          nest
            (!^"match" ^^ to_coq false e ^^ dep_match_print ^^ !^"with"
           ^^ newline
            ^^ separate space
                 (cases
                 |> List.map (fun (p, existential_cast, e) ->
                        nest
                          (!^"|" ^^ Pattern.to_coq false p ^^ !^"=>"
                          ^^ to_coq_cast_existentials existential_cast e
                          ^^ newline)))
            ^^ (if is_with_default_case then
                if Option.is_some dep_match then
                  !^"|" ^^ !^"_" ^^ !^"=>" ^^ to_coq_ltac Discriminate
                  ^^ newline
                else
                  !^"|" ^^ !^"_" ^^ !^"=>"
                  ^^ !^"unreachable_gadt_branch"
                  ^^ newline
               else empty)
            ^^ !^"end"))
  | MatchExtensible (e, cases) -> (
      match cases with
      | [ case ] -> (
          (* When there is a single case, we always expect this case to be the
             default case so we do not pattern-match anything. *)
          match case with
          | _, body ->
              Pp.parens paren
              @@ nest
                   (!^"let" ^^ !^"'_" ^^ !^":=" ^^ to_coq false e ^^ !^"in"
                  ^^ newline ^^ to_coq false body))
      | _ ->
          nest
            (!^"match" ^^ to_coq false e ^^ !^"with" ^^ newline
            ^^ nest
                 (nest
                    (!^"|" ^^ !^"Build_extensible" ^^ !^"tag" ^^ !^"_"
                   ^^ !^"payload" ^^ !^"=>")
                 ^^ nest
                      (separate space
                         (cases
                         |> List.map (fun (p, e) ->
                                match p with
                                | None -> to_coq false e
                                | Some (tag, p, typ) ->
                                    nest
                                      (!^"if"
                                      ^^ nest
                                           (!^"String.eqb" ^^ !^"tag"
                                           ^^ !^("\"" ^ tag ^ "\""))
                                      ^^ !^"then")
                                    ^^ newline
                                    ^^ indent
                                         (nest
                                            ((match p with
                                             | Pattern.Tuple [] -> empty
                                             | _ ->
                                                 nest
                                                   (!^"let"
                                                   ^^ (match p with
                                                      | Pattern.Tuple
                                                          [ Pattern.Variable _ ]
                                                        ->
                                                          empty
                                                      | _ -> !^"'")
                                                   ^-^ Pattern.to_coq false p
                                                   ^^ !^":=")
                                                 ^^ nest
                                                      (!^"cast"
                                                      ^^ Type.to_coq None
                                                           (Some
                                                              Type.Context.Apply)
                                                           typ
                                                      ^^ !^"payload" ^^ !^"in")
                                                 ^^ newline)
                                            ^^ to_coq false e))
                                    ^^ newline ^^ !^"else"))))
            ^^ newline ^^ !^"end"))
  | Record fields ->
      nest
        (!^"{|"
        ^^ separate space
             (fields
             |> List.map (fun (x, arity, e) ->
                    nest
                      (nest
                         (PathName.to_coq x
                         ^^ separate space (Pp.n_underscores arity)
                         ^^ !^":=")
                      ^^ to_coq false e ^-^ !^";")))
        ^^ !^"|}")
  | Field (e, x) -> to_coq true e ^-^ !^".(" ^-^ PathName.to_coq x ^-^ !^")"
  | IfThenElse (e1, e2, e3) ->
      Pp.parens paren
      @@ nest
           (group_all (!^"if" ^^ indent (to_coq false e1) ^^ !^"then")
           ^^ newline
           ^^ indent (to_coq false e2)
           ^^ newline ^^ !^"else" ^^ newline
           ^^ indent (to_coq false e3))
  | Module fields ->
      group
        (!^"{|" ^^ newline
        ^^ indent
             (separate (!^";" ^^ newline)
                (fields
                |> List.map (fun (x, nb_free_vars, e) ->
                       nest
                         (group
                            (nest
                               (PathName.to_coq x
                               ^^
                               match nb_free_vars with
                               | 0 -> empty
                               | _ ->
                                   nest
                                     (separate space
                                        (Pp.n_underscores nb_free_vars)))
                            ^^ !^":=")
                         ^^ to_coq false e))))
        ^^ newline ^^ !^"|}")
  | ModulePack (modul_typ_params, e) ->
      Pp.parens paren @@ nest (to_coq_exist_s modul_typ_params (to_coq true e))
  | Functor (x, typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"fun"
           ^^ parens
                (nest (Name.to_coq x ^^ !^":" ^^ Type.to_coq None None typ))
           ^^ !^"=>" ^^ to_coq false e)
  | Cast (e, typ) ->
      Pp.parens paren
      @@ nest
           (!^"cast"
           ^^ Type.to_coq None (Some Type.Context.Apply) typ
           ^^ to_coq true e)
  | TypAnnotation (e, typ) ->
      parens @@ nest (to_coq true e ^^ !^":" ^^ Type.to_coq None None typ)
  | Assert (typ, e) ->
      Pp.parens paren
      @@ nest
           (!^"assert"
           ^^ Type.to_coq None (Some Type.Context.Apply) typ
           ^^ to_coq true e)
  | Error message -> !^message
  | ErrorArray es -> OCaml.list (to_coq false) es
  | ErrorTyp typ -> Pp.parens paren @@ Type.to_coq None None typ
  | ErrorMessage (e, error_message) ->
      group (Error.to_comment error_message ^^ newline ^^ to_coq paren e)
  | Ltac tac -> to_coq_ltac tac

and to_coq_ltac (tac : ltac) : SmartPrint.t =
  !^"ltac:" ^-^ parens (to_coq_tac tac)

and to_coq_tac (tac : ltac) : SmartPrint.t =
  match tac with
  | Subst -> !^"subst"
  | Discriminate -> !^"discriminate"
  | Exact t -> !^"exact" ^^ to_coq true t
  | Concat (t1, t2) ->
      separate (!^";" ^^ space) [ to_coq_tac t1; to_coq_tac t2 ]

and to_coq_try_single_let_pattern (paren : bool) (let_symbol : string option)
    (e : t) (cases : (Pattern.t * match_existential_cast option * t) list)
    (is_with_default_case : bool) : SmartPrint.t option =
  match (cases, is_with_default_case) with
  | [ (pattern, existential_cast, e2) ], false
    when not (Pattern.has_or_patterns pattern) ->
      Some
        (Pp.parens paren
        @@ nest
             (to_coq_let_symbol let_symbol
             ^^ !^"'"
             ^-^ Pattern.to_coq false pattern
             ^-^ !^" :=" ^^ to_coq false e ^^ !^"in" ^^ newline
             ^^ to_coq_cast_existentials existential_cast e2))
  | _ -> None

and to_coq_cast_existentials (existential_cast : match_existential_cast option)
    (e : t) : SmartPrint.t =
  let e =
    match existential_cast with
    | Some { return_typ; cast_result = true; _ } ->
        group
          (nest
             (!^"cast" ^^ Type.to_coq None (Some Type.Context.Apply) return_typ)
          ^^ to_coq true e)
    | _ -> to_coq false e
  in
  match existential_cast with
  | None -> e
  | Some { new_typ_vars; bound_vars; use_axioms; enable; _ } -> (
      let variable_names =
        Pp.primitive_tuple
          (bound_vars |> List.map (fun (name, _) -> Name.to_coq name))
      in
      let variable_typ paren =
        match bound_vars with
        | [ (_, typ) ] ->
            let context = if paren then Some Type.Context.Apply else None in
            Type.to_coq None context typ
        | _ ->
            Pp.primitive_tuple_type
              (bound_vars
              |> List.map (fun (_, typ) -> Type.to_coq None None typ))
      in
      match (enable, bound_vars, new_typ_vars) with
      | false, _, _ | _, [], _ -> e
      | _, _, [] ->
          if use_axioms then
            let variable_names_pattern =
              match bound_vars with
              | [ _ ] -> variable_names
              | _ -> !^"'" ^-^ variable_names
            in
            nest
              (!^"let" ^^ variable_names_pattern ^^ !^":="
              ^^ nest (!^"cast" ^^ variable_typ true ^^ variable_names)
              ^^ !^"in" ^^ newline ^^ e)
          else e
      | _ ->
          let new_typ_vars_names =
            List.map (fun var -> Name.to_coq @@ fst var) new_typ_vars
          in
          let new_typ_vars_kinds =
            List.map (fun var -> Kind.to_coq @@ snd var) new_typ_vars
          in
          let existential_names = Pp.primitive_tuple new_typ_vars_names in
          let existential_names_pattern =
            Pp.primitive_tuple_pattern new_typ_vars_names
          in
          nest
            (!^"let" ^^ !^"'existT" ^^ !^"_" ^^ existential_names
           ^^ variable_names ^^ !^":="
            ^^ nest
                 (let operator, option =
                    if use_axioms then ("cast_exists", "Es") else ("existT", "A")
                  in
                  !^operator
                  ^^ nest
                       (parens
                          (!^option ^^ !^":="
                          ^^ Pp.primitive_tuple_type new_typ_vars_kinds))
                  ^^ parens
                       (nest
                          (!^"fun" ^^ existential_names_pattern ^^ !^"=>"
                         ^^ variable_typ false))
                  ^^ (if use_axioms then empty
                     else Pp.primitive_tuple_infer (List.length new_typ_vars))
                  ^^ variable_names)
            ^^ !^"in" ^^ newline ^^ e))

and to_coq_exist_s (module_typ_params : int Tree.t) (e : SmartPrint.t) :
    SmartPrint.t =
  let arities =
    Tree.flatten module_typ_params |> List.map (fun (_, arity) -> arity)
  in
  let typ_names = Tree.flatten module_typ_params |> List.map (fun _ -> !^"_") in
  let nb_of_existential_variables = List.length typ_names in
  nest
    (!^"existS"
    ^^ parens
         (nest
            (!^"A :=" ^^ Pp.primitive_tuple_type (List.map Pp.typ_arity arities)))
    ^^ (match nb_of_existential_variables with
       | 0 -> !^"(fun _ => _)"
       | _ -> !^"_")
    ^^ Pp.primitive_tuple typ_names
    ^^ e)
