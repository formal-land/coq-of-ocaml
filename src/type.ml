(** A type, with free type variables for polymorphic arguments. *)
open Types
open SmartPrint
open Monad.Notations

type t =
  | Variable of Name.t
  | Kind of Kind.t
  | Arrow of t * t
  | Eq of t * t
  | Sum of (string * t) list
  | Tuple of t list
  (* Application holds the information of what are tags *)
  | Apply of MixedPath.t * (t * bool) list
  | Signature of PathName.t * (Name.t * t option) list
  | ForallModule of Name.t * t * t
  | ExistTyps of (Name.t * int) list * t
  | ForallTyps of (Name.t * int) list * t
  | String of string
  | FunTyps of Name.t list * t
  | Error of string

type arity_or_typ =
  | Arity of int
  | Typ of t

let tag_constructor_of
    (typ : t) =
  match typ with
  | Variable a -> "var " ^ (Name.to_string a)
  | Arrow _ -> "arrow"
  | Eq _ -> "eq"
  | Sum _ -> "sum"
  | Tuple _ -> "tuple"
  | Apply (mpath, _) -> MixedPath.to_string mpath
  | Signature _ -> "signature"
  | ForallModule _ -> "forallModule"
  | ExistTyps _ -> "existsTyps"
  | ForallTyps _ -> "forallTyps"
  | FunTyps _ -> "funTyps"
  | Error s -> "error" ^ s
  | Kind k -> Kind.to_string k
  | String s -> "string"


let rec tag_typ_constr_aux
    (typ : t)
  : t Monad.t =
  let tag_ty = tag_typ_constr_aux in
  match typ with
  | Arrow (t1, t2) ->
    let* t1 = tag_ty t1 in
    let* t2 = tag_ty t2 in
    let tag = Name.arrow_tag |> MixedPath.of_name  in
    return (Apply (tag, List.combine [t1; t2] [false; false]))
  | Tuple ts ->
    let tag = Name.tuple_tag |> MixedPath.of_name  in
    let bs = [false; false] in
    if List.length ts = 2
    then
      let* ts = Monad.List.map tag_ty ts in
      return (Apply (tag, List.combine ts bs))
    else
      let* t = tag_ty (List.hd ts) in
      let* ts = tag_ty @@ Tuple (List.tl ts) in
      return (Apply (tag, List.combine [t; ts] bs))
  | Apply (mpath, ts) ->
    let (ts, bs) = List.split ts in
    let* ts = Monad.List.map tag_ty ts in
    let arg_names = List.map tag_constructor_of ts in
    let tag = Name.constr_tag |> MixedPath.of_name  in
    let name = (MixedPath.to_string mpath) in
    let str_repr = name ^
                   (List.fold_left (fun acc ty -> acc ^ "_" ^ ty) "" arg_names) in
    return (Apply (tag, List.combine [String str_repr; typ] [false; false]))
  | _ -> return typ


let type_exprs_of_row_field (row_field : Types.row_field)
  : Types.type_expr list =
  match row_field with
  | Rpresent None -> []
  | Rpresent (Some typ) -> [typ]
  | Reither (_, typs, _, _) -> typs
  | Rabsent -> []

let filter_typ_params_in_valid_set
  (typ_params : AdtParameters.AdtVariable.t list) (valid_set : Name.Set.t) : bool list =
  typ_params |> List.map (function
      | AdtParameters.AdtVariable.Parameter name -> Name.Set.mem name valid_set
      | _ -> false )

let rec non_phantom_typs (path : Path.t) (typs : Types.type_expr list)
  : Types.type_expr list Monad.t =
  get_env >>= fun env ->
  begin match Env.find_type path env with
  | typ_declaration ->
    AdtParameters.of_ocaml typ_declaration.type_params >>= fun typ_params ->
    Attribute.of_attributes typ_declaration.type_attributes >>= fun typ_attributes ->
    let is_phantom = Attribute.has_phantom typ_attributes in
    let is_tagged = Attribute.has_tag_gadt typ_attributes in
    if is_phantom then
      return (Some (typ_params |> List.map (fun _ -> false)))
    else if is_tagged then
      return None
    (* This is both an optimization and a way to avoid infinite loops on some
       recursive types, such as recursive records (although we do not support
       recursive records on the Coq side). *)
    else if List.length typ_params = 0 then
      return (Some [])
    else
      begin match typ_declaration.type_kind with
      | Type_abstract ->
        begin match typ_declaration.type_manifest with
        | None ->
          return (Some (typ_params |> List.map (function
            | AdtParameters.AdtVariable.Parameter _ -> true
            | _ ->
              if Path.name path = "array" then
                true
              else
                false
          )))
        (* Specific case for inductives defined with polymorphic variants. *)
        | Some { desc = Tvariant _; _ } ->
          return (Some (typ_params |> List.map (function
            | AdtParameters.AdtVariable.Parameter _ -> true
            | _ -> false
          )))
        | Some typ ->
          non_phantom_vars_of_typ typ >>= fun non_phantom_typ_vars ->
          return (Some (
            filter_typ_params_in_valid_set typ_params non_phantom_typ_vars
          ))
        end
      | Type_record (labels, _) ->
        let typs = List.map (fun label -> label.ld_type) labels in
        non_phantom_vars_of_typs typs >>= fun non_phantom_typ_vars ->
        return (Some (
          filter_typ_params_in_valid_set typ_params non_phantom_typ_vars
        ))
      | Type_variant constructors ->
        let* constructors_return_typ_params =
          constructors |> Monad.List.map (fun constructor ->
              AdtParameters.get_return_typ_params typ_params constructor.cd_res
            ) in
        let gadt_shape = AdtParameters.gadt_shape typ_params constructors_return_typ_params in
        return (Some (gadt_shape |> List.map (fun shape ->
            match shape with
            | None -> false
            | Some _ -> not (Attribute.has_force_gadt typ_attributes)
          )))
      | Type_open -> return None
      end
    | exception Not_found -> return None
    end >>= fun non_phantom_typs_shape ->
  let typs =
    match non_phantom_typs_shape with
    | None -> typs
    | Some non_phantom_typs_shape ->
      List.rev @@ List.fold_left2
        (fun typs is_non_phantom typ ->
          if is_non_phantom then
            typ :: typs
          else
            typs
        )
        [] non_phantom_typs_shape typs in
  return typs

and non_phantom_vars_of_typ (typ : Types.type_expr) : Name.Set.t Monad.t =
  match typ.desc with
  | Tvar x | Tunivar x ->
    begin match x with
    | None -> return Name.Set.empty
    | Some x ->
      let* x = Name.of_string false x in
      return (Name.Set.singleton x)
    end
  | Tconstr (path, typs, _) ->
    non_phantom_typs path typs >>= fun typs ->
    non_phantom_vars_of_typs typs
  | Tarrow (_, typ1, typ2, _) -> non_phantom_vars_of_typs [typ1; typ2]
  | Ttuple typs | Tpackage (_, _, typs) ->
    non_phantom_vars_of_typs typs
  | Tlink typ | Tsubst typ -> non_phantom_vars_of_typ typ
  | Tobject (_, object_descr) ->
    let param_typs =
      match !object_descr with
      | Some (_, _ :: param_typs) -> List.tl param_typs
      | _ -> [] in
    non_phantom_vars_of_typs param_typs
  | Tfield (_, _, typ1, typ2) -> non_phantom_vars_of_typs [typ1; typ2]
  | Tnil -> return Name.Set.empty
  | Tvariant _ ->
    (* We return an empty set to prevent a potential stack-overflow. Moreover,
       one should note that for the case of type synonyms which are polymorphic
       variants we directly consider this definition like an inductive
       definition in the phantom types analysis. *)
    return Name.Set.empty
  | Tpoly (typ, typ_args) ->
    let* typ_args =
      AdtParameters.typ_params_ghost_marked typ_args in
    let typ_args =
      typ_args |>
      AdtParameters.get_parameters |>
      Name.Set.of_list in
    non_phantom_vars_of_typ typ >>= fun non_phantom_vars ->
    return (Name.Set.diff non_phantom_vars typ_args)

and non_phantom_vars_of_typs (typs : Types.type_expr list) 
  : Name.Set.t Monad.t =
  Monad.List.fold_left
    (fun typ_vars typ ->
      non_phantom_vars_of_typ typ >>= fun new_typ_vars ->
      return (Name.Set.union typ_vars new_typ_vars)
    )
    Name.Set.empty
    typs

let subst_name (source : Name.t) (target : Name.t) (typ : t) : t =
  let rec subst (typ : t) : t =
    let subst_after_names (names : Name.t list) (typ : t) : t =
      let should_substitute =
        not (names |> List.exists (fun name -> Name.equal name source)) in
      if should_substitute then
        subst typ
      else
        typ in
    let subst_after_names_with_arity (names : (Name.t * int) list) (typ : t)
      : t =
      subst_after_names (List.map fst names) typ in
    match typ with
    | Variable name ->
      if Name.equal name source then
        Variable target
      else
        typ
    | Arrow (typ1, typ2) -> Arrow (subst typ1, subst typ2)
    | Sum tagged_typs ->
      Sum (tagged_typs |> List.map (fun (tag, typ) -> (tag, subst typ)))
    | Tuple typs -> Tuple (List.map subst typs)
    | Apply (constructor, typs) ->
        let constructor_with_subst =
          match constructor with
          | PathName { path = []; base } when Name.equal base source ->
            MixedPath.PathName { path = []; base = target }
          | _ -> constructor in
        let (ts, bs) = List.split typs in
        let ts = List.map subst ts in
        let typs = List.combine ts bs in
      Apply (constructor_with_subst, typs)
    | Signature (path_name, typ_params) ->
      Signature (
        path_name,
        typ_params |>
        List.map (fun (name, typ) -> (name, Option.map subst typ))
      )
    | ExistTyps (typ_params, typ) ->
      ExistTyps (typ_params, subst_after_names_with_arity typ_params typ)
    | ForallModule (name, typ1, typ2) ->
      ForallModule (name, subst typ1, subst typ2)
    | ForallTyps (names, typ) ->
      ForallTyps (names, subst_after_names_with_arity names typ)
    | FunTyps (names, typ) -> FunTyps (names, subst_after_names names typ)
    | _ -> typ in
  subst typ

let apply_with_notations (mixed_path : MixedPath.t) (typs : t list) (tag_list : bool list)
  : t Monad.t =
  let* configuration = get_configuration in
  let mixed_path =
    let renaming =
      Configuration.is_in_renaming_type_constructor
        configuration (MixedPath.to_string mixed_path) in
    match renaming with
    | Some renaming -> MixedPath.of_name (Name.of_string_raw renaming)
    | None -> mixed_path in
  (* The following notation is very specific. So we let it there in the code,
     instead of adding a configuration option. *)
  let (mixed_path, typs, tag_list) =
    match (mixed_path, typs) with
    | (
        MixedPath.PathName {
          path = [Name.Make "Pervasives"];
          base = Name.Make "result"
        },
        [
          typ1;
          Apply (
            MixedPath.PathName {
              path = [Name.Make "Error_monad"];
              base = Name.Make "trace"
            },
            _
          )
        ]
      ) -> (MixedPath.of_name (Name.of_string_raw "M?"), [typ1], [false])
    | _ -> (mixed_path, typs, tag_list) in
  let apply_with_merge =
    match (mixed_path, typs) with
    | (
        MixedPath.PathName { path = []; base = Name.Make source1 },
        [
          Apply (
            MixedPath.PathName { path = []; base = Name.Make source2 },
            typs
          )
        ]
      ) ->
      let target =
        Configuration.is_in_merge_types configuration source1 source2 in
      begin match target with
      | Some target ->
        Some (
          Apply (
            MixedPath.PathName { path = []; base = Name.Make target },
            typs
          )
        )
      | None -> None
      end
    | _ -> None in
  match apply_with_merge with
  | None -> return (Apply (mixed_path, List.combine typs tag_list))
  | Some apply_with_merge -> return apply_with_merge

(** Heuristic to find a simpler alias if the path is in a module as a record. *)
let simplified_contructor_path (path : Path.t) (arity : int)
  : MixedPath.t Monad.t =
  let* mixed_path = MixedPath.of_path false path in
  match mixed_path with
  | Access _ ->
    let* path = PathName.iterate_in_aliases path arity in
    begin try
      (* By calling this function we check that we do not have a path with
         functors, which we cannot handle. *)
      let _ = MixedPath.path_to_string_list path in
      MixedPath.of_path false path
    with _ -> return mixed_path
    end
  | _ -> return mixed_path


let is_native_type
    (typ : t)
  : bool =
  match typ with
  | Variable var -> List.mem (Name.to_string var) Name.native_types
  | Apply (mpath, _) -> MixedPath.is_native_type mpath
  | _ -> false

let print_type
    (path : Path.t)
  : unit Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | typ -> return @@ Printtyp.type_declaration (Ident.create_local "a") Format.std_formatter  typ
  | exception _ -> return ()

let has_type_manifest
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_manifest = Some _; _ } -> return @@ true
  | _ | exception _ -> return false

let is_type_variant (t : Types.type_expr) : bool Monad.t =
  match t.desc with
  | Tconstr (path, _, _) ->
    let* is_variant = PathName.is_variant_declaration path in
    return @@ Option.is_some is_variant
  | _ -> return false

let rec tag_all_args : 'a. 'a list -> bool list = function
  | [] -> []
  | x :: xs -> true :: tag_all_args xs

let rec tag_no_args : 'a. 'a list -> bool list = function
  | [] -> []
  | x :: xs -> false :: tag_no_args xs

let tag_args_with (b : bool) : 'a list -> bool list =
  if b
  then tag_all_args
  else tag_no_args

(** This function is utilized for building dependent pattern matching,
    if typ is a type constructor then it will return a list of equations
    relating each index of the type constructor to its real instantiation *)
let normalize_constructor (typ : t) : t * t list =
  match typ with
  | Apply (t, args) ->
    let (args, bs) = List.split args in
    let (args, eqs) = args |> List.mapi (fun i typ ->
        let x = "t" ^ string_of_int i |> Name.of_string_raw in
        (Variable x, Eq (Variable x, typ))
      ) |> List.split in
    (Apply (t, List.combine args bs), eqs)
  | _ -> (typ, [])


let is_type_abstract
    (path : Path.t)
  : bool Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_abstract; _ } -> return @@ true
  | _ | exception _ ->
    return false

(** Import an OCaml type. Add to the environment all the new free type variables. *)
let rec of_typ_expr
  ?(should_tag = false)
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * VarEnv.t) Monad.t =
  match typ.desc with
  | Tvar x | Tunivar x ->
    (match x with
    | None ->
      if with_free_vars then
        let n = Name.Map.cardinal typ_vars in
        return (Printf.sprintf "A%d" typ.id, String.make 1 (Char.chr (Char.code 'A' + n)))
      else
        raise ("_", "_") NotSupported "The placeholders `_` in types are not handled"
    | Some x -> return (x, x)
    ) >>= fun (source_name, generated_name) ->
    let* source_name = Name.of_string false source_name in
    let* generated_name = Name.of_string false generated_name in
    let typ = if should_tag
      then Kind.Tag
      else Kind.Set in
    let (typ_vars, new_typ_vars, name) =
      if Name.Map.mem source_name typ_vars then (
        let name = Name.Map.find source_name typ_vars in
        (typ_vars, [(name, typ)], name)
      ) else (
        let typ_vars = Name.Map.add source_name generated_name typ_vars in
        (typ_vars, [(generated_name, typ)], generated_name)
      ) in
    return (Variable name, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ_x >>= fun (typ_x, typ_vars, new_typ_vars_x) ->
    of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ_y >>= fun (typ_y, typ_vars, new_typ_vars_y) ->
    let new_typ_vars = VarEnv.union new_typ_vars_x new_typ_vars_y in
    return (Arrow (typ_x, typ_y), typ_vars, new_typ_vars)
  | Ttuple typs ->
    let tag_list = tag_args_with should_tag typs in
    of_typs_exprs ~tag_list:tag_list with_free_vars typs typ_vars >>= fun (typs, typ_vars, new_typ_vars) ->
    return (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    non_phantom_typs path typs >>= fun typs ->
    let* mixed_path = simplified_contructor_path path (List.length typs) in
    let* is_abstract = is_type_abstract path in
    let native_type = List.mem (MixedPath.to_string mixed_path) Name.native_types in
    let is_pident = match path with
      | Path.Pident _ -> true
      | _ -> false in
    let* is_tagged_variant = PathName.is_tagged_variant path in
    if not is_tagged_variant
    then begin
      let tag_list = tag_no_args typs in
      let* (typs, typ_vars, new_typs_vars) = of_typs_exprs with_free_vars typs typ_vars in
      let* typ = apply_with_notations mixed_path typs tag_list in
      return (typ, typ_vars, new_typs_vars)
    end
    (* For unknown reasons a type variable becomes a Tconstr some times (see type of patterns)
       This `if` is to try to figure out if such constructor was supposed to be a variable *)
    else if is_abstract && not native_type && is_pident && List.length typs = 0
    then begin
      let var_name = (Name.of_last_path path) in
      let var = Variable var_name in
      let* new_typ_vars =
        if should_tag
        then return [(var_name, Kind.Tag)]
        else return [(var_name, Kind.Set)]
      in
      return @@ (var , typ_vars, new_typ_vars)
    end
    else
      let* tag_list = get_constr_arg_tags path in
      let* (typs, typ_vars, new_typs_vars) = of_typs_exprs ~tag_list:tag_list with_free_vars typs typ_vars in
      let* typs = tag_typ_constr path typs in
      let* typ = apply_with_notations mixed_path typs tag_list in
      return (typ, typ_vars, new_typs_vars)

  | Tobject (_, object_descr) ->
    begin match !object_descr with
    | Some (path, _ :: typs) ->
      let tag_list = tag_args_with should_tag typs in
      of_typs_exprs ~tag_list:tag_list with_free_vars typs typ_vars >>= fun (typs, typ_vars, new_typ_vars) ->
      let are_tags = tag_no_args typs in
      MixedPath.of_path false path >>= fun mixed_path ->
      return (Apply (mixed_path, List.combine typs are_tags), typ_vars, new_typ_vars)
    | _ ->
      raise
        (Error "unhandled_object_type", typ_vars, [])
        NotSupported
        "We do not handle this form of object types"
    end
  | Tfield (_, _, typ1, typ2) ->
    of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ1 >>= fun (typ1, typ_vars, new_typ_vars1) ->
    of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ2 >>= fun (typ2, typ_vars, new_typ_vars2) ->
    raise
      (
        Tuple [typ1; typ2],
        typ_vars,
        VarEnv.union new_typ_vars1 new_typ_vars2
      )
      NotSupported "Field types are not handled"
  | Tnil ->
    raise
      (Error "nil", typ_vars, [])
      NotSupported
      "Nil type is not handled"
  | Tlink typ | Tsubst typ -> of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ
  | Tvariant { row_fields; _ } ->
    PathName.typ_of_variants (List.map fst row_fields) >>= fun path_name ->
    begin match path_name with
    | Some path_name ->
      return (
        Apply (MixedPath.PathName path_name, []),
        typ_vars,
        []
      )
    | None ->
      Monad.List.fold_left
        (fun (fields, typ_vars, new_typ_vars) (name, row_field) ->
          let typs = type_exprs_of_row_field row_field in
          let tag_list = tag_args_with should_tag typs in
          of_typs_exprs ~tag_list:tag_list with_free_vars typs typ_vars >>= fun (typs, typ_vars, new_typ_vars') ->
          return (
            (name, Tuple typs) :: fields,
            typ_vars,
            VarEnv.union new_typ_vars new_typ_vars'
          )
        )
        ([], typ_vars, [])
        row_fields >>= fun (fields, typ_vars, new_typ_vars) ->
      return (Sum (List.rev fields), typ_vars, new_typ_vars)
    end
  | Tpoly (typ, typ_args) ->
    let* typ_args =
      AdtParameters.typ_params_ghost_marked typ_args in
    let typ_args = typ_args |> AdtParameters.get_parameters in
    non_phantom_vars_of_typ typ >>= fun non_phantom_vars ->
    let typ_args = typ_args |> List.filter_map (fun typ_arg ->
      if Name.Set.mem typ_arg non_phantom_vars then
        Some (typ_arg, 0)
      else
        None
    ) in
    of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars_typ) ->
    let non_phantom_vars = Name.Set.elements non_phantom_vars in
    let new_typ_vars_typ = VarEnv.keep_only non_phantom_vars new_typ_vars_typ in
    return (ForallTyps (typ_args, typ), typ_vars, new_typ_vars_typ)
  | Tpackage (path, idents, typs) ->
      let* path_name = PathName.of_path_without_convert false path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let path = Longident.flatten ident in
          of_typ_expr ~should_tag:false with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
          return (
            (path, typ) :: typ_substitutions,
            typ_vars,
            VarEnv.union new_typ_vars new_typ_vars'
          )
        )
        ([], typ_vars, [])
        typ_substitutions >>= fun (typ_substitutions, typ_vars, new_typ_vars) ->
      get_env >>= fun env ->
      let module_typ = Env.find_modtype path env in
      ModuleTypParams.get_module_typ_declaration_typ_params_arity
        module_typ >>= fun signature_typ_params ->
      let typ_params = List.fold_left
        (fun typ_values (path, typ) ->
          Tree.map_at typ_values path (fun _ -> Typ typ)
        )
        (signature_typ_params |> Tree.map (fun arity -> Arity arity))
        typ_substitutions in
      let typ_params = Tree.flatten typ_params in
      let* exist_vars =
        typ_params |>
        Monad.List.filter_map (fun (path, arity_or_typ) ->
          match arity_or_typ with
          | Arity arity ->
            let* name = Name.of_strings false path in
            return (Some (name, arity))
          | Typ _ -> return None
        ) in
      let* signature_params =
        typ_params |>
        Monad.List.map (fun (path, arity_or_typ) ->
          let* name = Name.of_strings false path in
          match arity_or_typ with
          | Arity _ -> return (name, Some (Variable name))
          | Typ typ -> return (name, Some typ)
        ) in
      return (
        ExistTyps (exist_vars, Signature (path_name, signature_params)),
        typ_vars,
        new_typ_vars
      )

and of_typs_exprs
    (with_free_vars: bool)
    (typs : Types.type_expr list)
    ?(tag_list = tag_no_args typs)
    (typ_vars : Name.t Name.Map.t)
  : (t list * Name.t Name.Map.t * VarEnv.t) Monad.t =
  if List.length tag_list <> List.length typs
  then raise ([], typ_vars, []) Error.Category.Unexpected ("of_typs_exprs_constr: tag_list has size " ^ string_of_int (List.length tag_list) ^ ", while typs has size " ^ string_of_int (List.length typs) ^ ". They should have the same size")
  else let tag_typs = List.combine typs tag_list in
    (Monad.List.fold_left
       (fun (typs, typ_vars, new_typ_vars) (typ, should_tag) ->
          of_typ_expr ~should_tag:should_tag with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
          let new_typ_vars = VarEnv.union new_typ_vars new_typ_vars' in
          return (typ :: typs, typ_vars, new_typ_vars)
       )
       ([], typ_vars, [])
       tag_typs
    ) >>= fun (typs, typ_vars, new_typ_vars) ->
    return (List.rev typs, typ_vars, new_typ_vars)


and get_constr_arg_tags
    (path : Path.t)
    : bool list Monad.t =
  let* env = get_env in
  match Env.find_type path env with
  | { type_kind = Type_variant _; type_params = params; type_attributes = attributes; _ } ->
    let* attributes = Attribute.of_attributes attributes in
    if Attribute.has_tag_gadt attributes
    then return @@ tag_all_args params
    else return @@ tag_no_args params
  | { type_kind = Type_record (decls, repr); type_params = params; _} ->
    (* Get the variables from param. Keep ordering *)
    let* (_, _, typ_vars) = of_typs_exprs true params Name.Map.empty in
    let typ_vars = List.map (fun (ty, _) -> ty) typ_vars in
    let decls =  List.map (fun decl -> decl.ld_type) decls in
    let* (_, _, new_typ_vars) = of_typs_exprs true decls Name.Map.empty in
    let new_typ_vars = VarEnv.reorg typ_vars new_typ_vars in
    return @@ List.map (fun (_, kind) ->
        match kind with
        | Kind.Tag -> true
        | _ -> false
      ) new_typ_vars
  | { type_manifest = None; type_kind = Type_abstract; type_params = params; _ } ->
    return @@ tag_no_args params
  | { type_manifest = Some typ; type_params = params; _ } ->
    let* (typ, typ_vars, new_typ_vars) = of_typ_expr true Name.Map.empty typ in
    return @@ List.map (fun (_, kind) ->
        match kind with
        | Kind.Tag -> true
        | _ -> false
      ) new_typ_vars
  | _ | exception _ -> return []

and tag_typ_constr
    (path : Path.t)
    (typs : t list)
  : t list Monad.t =
  let* is_tagged_variant = PathName.is_tagged_variant path in
  if not is_tagged_variant
  then raise [] Error.Category.Unexpected "You shouldn't call tag_typ_constr on a non_tagged variant"
  else if PathName.is_native_datatype path
  then return typs
  else
    let* should_tag_list = get_constr_arg_tags path in
    let* name = MixedPath.of_path false path in
    let tag_typs = List.combine typs should_tag_list in
    Monad.List.map (fun (typ, should_tag) ->
        if should_tag
        then tag_typ_constr_aux typ
        else return typ
      ) tag_typs

let rec decode_var_tags_aux
    (typ_vars : VarEnv.t)
    (in_native : bool)
    (is_tag : bool)
    (typ : t)
  : t Monad.t =
  let dec = decode_var_tags_aux typ_vars in_native is_tag in
  match typ with
  | Variable name ->
    begin
      if is_tag || in_native
      then return typ
      else match List.assoc_opt name typ_vars with
        | None -> return typ
        | Some Kind.Tag -> return @@ Apply (MixedPath.dec_name, [(typ, true)])
        | Some _ -> return typ
    end
  | Arrow (t1, t2) ->
    let* t1 = decode_var_tags_aux typ_vars in_native true t1 in
    let* t2 = decode_var_tags_aux typ_vars in_native true t2 in
    return @@ Arrow (t1, t2)
  | Tuple ts ->
    let* ts = Monad.List.map (decode_var_tags_aux typ_vars in_native true) ts in
    return @@ Tuple ts
  | Apply (mpath, ts) ->
    let (ts, bs) = List.split ts in
    let path_str = MixedPath.to_string mpath in
    let in_native = List.mem path_str ["tuple_tag"; "arrow_tag"; "list_tag"; "option_tag"] in
    let dec = decode_var_tags_aux typ_vars in_native in
    let ts = List.combine ts bs in
    let* ts = Monad.List.map (fun (t, b) -> dec b t) ts in
    return @@ Apply (mpath, List.combine ts bs)
  | ForallModule (name, t1, t2) ->
    let* t1 = dec t1 in
    let* t2 = dec t2 in
    return @@ ForallModule (name, t1, t2)
  | ForallTyps (names, t) ->
    let* t = dec t in
    return @@ ForallTyps (names, t)
  | FunTyps (names, t) ->
    let* t = dec t in
    return @@ FunTyps (names, t)
  | _ -> return typ


let rec decode_var_tags
    (typ_vars : VarEnv.t)
    (is_tag : bool)
    (typ : t)
  : t Monad.t = decode_var_tags_aux typ_vars false is_tag typ


let rec of_type_expr_variable (typ : Types.type_expr) : Name.t Monad.t =
  match typ.desc with
  | Tvar (Some x) | Tunivar (Some x) -> Name.of_string false x
  | Tlink typ | Tsubst typ -> of_type_expr_variable typ
  | _ ->
    raise
      (Name.of_string_raw "expected_variable")
      NotSupported
      "Only type variables are supported as parameters."

let of_type_expr_without_free_vars (typ : Types.type_expr) : t Monad.t =
  of_typ_expr false Name.Map.empty typ >>= fun (typ, _, _) ->
  return typ

(** We do not generate error messages for this function. Indeed, if there are
    errors for the following types, they should be noticed elsewhere (by the
    conversion function to Coq for example). *)
let rec existential_typs_of_typ (typ : Types.type_expr) : Name.Set.t Monad.t =
  match typ.desc with
  | Tvar _ | Tunivar _ -> return Name.Set.empty
  | Tarrow (_, typ_x, typ_y, _) -> existential_typs_of_typs [typ_x; typ_y]
  | Ttuple typs -> existential_typs_of_typs typs
  | Tconstr (path, typs, _) ->
    get_env >>= fun env ->
    let* path_existential =
      match path with
      | Path.Pident ident ->
        begin match Env.find_type path env with
        | _ -> return Name.Set.empty
        | exception Not_found ->
          let* ident = Name.of_ident false ident in
          return (Name.Set.singleton ident)
        end
      | _ -> return Name.Set.empty in
    existential_typs_of_typs typs >>= fun existentials ->
    return (Name.Set.union path_existential existentials)
  | Tobject (_, object_descr) ->
    let param_typs =
      match !object_descr with
      | Some (_, _ :: param_typs) -> List.tl param_typs
      | _ -> [] in
    existential_typs_of_typs param_typs
  | Tfield (_, _, typ1, typ2) -> existential_typs_of_typs [typ1; typ2]
  | Tnil -> return Name.Set.empty
  | Tlink typ | Tsubst typ -> existential_typs_of_typ typ
  | Tvariant { row_fields; _ } ->
    existential_typs_of_typs (
      row_fields |>
      List.map (fun (_, row_field) -> type_exprs_of_row_field row_field) |>
      List.concat
    )
  | Tpoly (typ, typs) -> existential_typs_of_typs (typ :: typs)
  | Tpackage (_, _, typs) -> existential_typs_of_typs typs

and existential_typs_of_typs (typs : Types.type_expr list)
  : Name.Set.t Monad.t =
  Monad.List.fold_left
    (fun existentials typ ->
      existential_typs_of_typ typ >>= fun existentials_typ ->
      return (Name.Set.union existentials existentials_typ)
    )
    Name.Set.empty typs

(** The free variables of a type. *)
let rec typ_args_of_typ (typ : t) : Name.Set.t =
  let diff_typ_names (typ : t) (names : Name.t list) : Name.Set.t =
    Name.Set.diff (typ_args_of_typ typ) (Name.Set.of_list names) in
  match typ with
  | Kind _ | String _ -> Name.Set.empty
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) | Eq (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Sum typs -> typ_args_of_typs (List.map snd typs)
  | Tuple typs -> typ_args_of_typs typs
  | Apply (_, typs) -> typs |> List.map (fun x -> fst x) |> typ_args_of_typs
  | Signature (_, typ_params) ->
    typ_params |>
    List.map (fun (_, typ) ->
      match typ with
      | None -> Name.Set.empty
      | Some typ -> typ_args_of_typ typ
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ExistTyps (typ_params, typ) ->
    let typ_params = List.map fst typ_params in
    diff_typ_names typ typ_params
  | ForallModule (_, param, result) ->
    Name.Set.union (typ_args_of_typ param) (typ_args_of_typ result)
  | ForallTyps (typ_params, typ) ->
    let typ_params = List.map fst typ_params in
    diff_typ_names typ typ_params
  | FunTyps (typ_params, typ) -> diff_typ_names typ typ_params
  | Error _ -> Name.Set.empty

and typ_args_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (typ_args_of_typ typ))
    Name.Set.empty typs

let rec nb_forall_typs (typ : t) : int =
  match typ with
  | ForallTyps (typ_params, typ) -> List.length typ_params + nb_forall_typs typ
  | _ -> 0

(** The local type constructors of a type. Used to detect the existential
    variables which are actually used by a type, once we remove the phantom
    types. *)
let rec local_typ_constructors_of_typ (typ : t) : Name.Set.t =
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) | Eq(typ1, typ2) -> local_typ_constructors_of_typs [typ1; typ2]
  | Sum typs -> local_typ_constructors_of_typs (List.map snd typs)
  | Tuple typs -> local_typ_constructors_of_typs typs
  | Apply (mixed_path, ts) ->
    let typs = List.map (fun x -> fst x) ts in
    let local_typ_constructors = local_typ_constructors_of_typs typs in
    begin match mixed_path with
    | MixedPath.PathName { path = []; base } ->
      Name.Set.add base local_typ_constructors
    | _ -> local_typ_constructors
    end
  | Signature (_, typ_params) ->
    typ_params |>
    List.map (fun (_, typ) ->
      match typ with
      | None -> Name.Set.empty
      | Some typ -> local_typ_constructors_of_typ typ
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ExistTyps (_, typ) -> local_typ_constructors_of_typ typ
  | ForallModule (_, param, result) ->
    local_typ_constructors_of_typs [param; result]
  | ForallTyps (_, typ) | FunTyps (_, typ) -> local_typ_constructors_of_typ typ
  | Error _ | Kind _ | String _ -> Name.Set.empty

and local_typ_constructors_of_typs (typs : t list) : Name.Set.t =
  List.fold_left (fun args typ -> Name.Set.union args (local_typ_constructors_of_typ typ))
    Name.Set.empty typs

(** In a function's type extract the body's type (up to [n] arguments). *)
let rec open_type (typ : t) (n : int) : t list * t =
  if n = 0 then
    ([], typ)
  else
    match typ with
    | Arrow (typ1, typ2) ->
      let (typs, typ) = open_type typ2 (n - 1) in
      (typ1 :: typs, typ)
    | _ -> failwith "Expected an arrow type."

(** The context to know if parenthesis are needed. *)
module Context = struct
  type t =
    | Apply
    | Arrow
    | Sum
    | Tuple
    | Forall
    | Eq

  let get_order (context : t) : int =
    match context with
    | Apply -> 0
    | Arrow -> 3
    | Sum -> 2
    | Tuple -> 1
    | Forall -> 4
    | Eq -> 5

  let should_parens (context : t option) (current_context : t) : bool =
    match context with
    | None -> false
    | Some context ->
      let order = get_order context in
      let current_order = get_order current_context in
      order <= current_order

  let parens
    (context : t option)
    (current_context : t)
    (doc : SmartPrint.t)
    : SmartPrint.t =
    Pp.parens (should_parens context current_context) doc
end

let rec accumulate_nested_arrows (typ : t) : t list * t =
  match typ with
  | Arrow (typ_x, typ_y) ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ_y in
    (typ_x :: typ_xs, typ_y)
  | _ -> ([], typ)

module Subst = struct
  type t = {
    path_name : PathName.t -> PathName.t }
end

let tag_notation (path : MixedPath.t) (typs : t list): t option =
  if not (MixedPath.is_constr_tag path) || List.length typs <> 2 then None
  else let typ = List.nth typs 1 in
    let name = tag_constructor_of typ in
    let tagged_name = (Name.of_string_raw (name ^ "_tag")) in
    if List.mem name Name.native_types
    then Some (Variable tagged_name)
    else match typ with
      | Apply (mname, ts) ->
        if List.mem name Name.native_type_constructors
        then Some (Apply (MixedPath.of_name tagged_name, ts))
        else None
      | _ -> None

let rec to_coq_typ_arity (arity : int) : SmartPrint.t =
  if arity = 0 then
    Pp.set
  else
    Pp.set ^^ !^ "->" ^^ to_coq_typ_arity (arity - 1)

type parens_or_braces =
  | Parens
  | Braces

let to_coq_grouped_typ_params (parens_or_braces : parens_or_braces)
  (typ_params : (Name.t * int) list) : SmartPrint.t =
  let typ_params : (SmartPrint.t * int) list =
    typ_params |> List.map (fun (name, arity) ->
      (Name.to_coq name, arity)
    ) in
  let reversed_grouped_typ_params : (SmartPrint.t list * int) list =
    List.fold_left
      (fun grouped (typ_param, arity) ->
        match grouped with
        | [] -> [([typ_param], arity)]
        | (typ_params, arity') :: grouped' ->
          if arity = arity' then
            (typ_param :: typ_params, arity') :: grouped'
          else
            ([typ_param], arity) :: grouped
      )
      []
      typ_params in
  let grouped_typ_params =
    reversed_grouped_typ_params |>
    List.map (fun (typ_params, arity) -> (List.rev typ_params, arity)) |>
    List.rev in
  separate space (grouped_typ_params |> List.map (fun (typ_params, arity) ->
    nest ((match parens_or_braces with Parens -> parens | Braces -> braces) (
      separate space typ_params ^^ !^ ":" ^^ to_coq_typ_arity arity
    ))
  ))

(** Pretty-print a type. Use the [context] parameter to know if we should add
    parenthesis. *)
let rec to_coq (subst : Subst.t option) (context : Context.t option) (typ : t)
  : SmartPrint.t =
  match typ with
  | String x -> !^ ("\"" ^ x ^ "\"")
  | Variable x -> Name.to_coq x
  | Arrow _ ->
    let (typ_xs, typ_y) = accumulate_nested_arrows typ in
    Context.parens context Context.Arrow @@ group (
      separate space (typ_xs |> List.map (fun typ_x ->
        group (to_coq subst (Some Context.Arrow) typ_x ^^ !^ "->"
      ))) ^^
      to_coq subst (Some Context.Arrow) typ_y
    )
  | Kind k -> Kind.to_coq k
  | Eq (lhs, rhs) ->
    Context.parens context Context.Eq @@ group (
        (to_coq subst (Some Context.Eq) lhs ^^ !^ "="
      )) ^^
      to_coq subst (Some Context.Eq) rhs
  | Sum typs ->
    let typs = typs |> List.map (fun (name, typ) ->
      let context = if List.length typs = 1 then context else Some Sum in
      group (nest (!^ "(*" ^^ !^ ("`" ^ name) ^^ !^ "*)") ^^ to_coq subst context typ)
    ) in
    begin match typs with
    | [] -> !^ "Empty_set"
    | [typ] -> typ
    | _ ->
      Context.parens context Context.Sum @@ nest @@
      separate (space ^^ !^ "+" ^^ space) typs
    end
  | Tuple typs ->
    begin match typs with
    | [] -> !^ "unit"
    | [typ] -> to_coq subst context typ
    | _ ->
      Context.parens context Context.Tuple @@ nest @@
      separate (space ^^ !^ "*" ^^ space)
        (List.map (to_coq subst (Some Context.Tuple)) typs)
    end
  | Apply (path, typs) ->
    let typs = List.map (fun t -> fst t) typs in
    begin match tag_notation path typs with
      | Some tag -> to_coq subst (Some Context.Apply) tag
      | None ->
        let path =
          match subst with
          | None -> path
          | Some subst ->
            begin match path with
              | MixedPath.PathName path_name ->
                MixedPath.PathName (subst.path_name path_name)
              | _ -> path
            end in
        Pp.parens (Context.should_parens context Context.Apply && typs <> []) @@
        nest @@ separate space
          (MixedPath.to_coq path :: List.map (to_coq subst (Some Context.Apply)) typs)
    end
  | Signature (path_name, typ_params) ->
    nest (separate space (
        PathName.to_coq path_name ::
      (typ_params |> List.map (fun (name, typ) ->
        nest (parens (
          Name.to_coq name ^^ !^ ":=" ^^
          begin match typ with
          | None -> !^ "_"
          | Some typ -> to_coq subst None typ
          end
        ))
      ))
    ))
  | ExistTyps (typ_params, typ) ->
      let existential_typs_pattern =
        typ_params |>
        List.map (fun (name, _) -> Name.to_coq name) |>
        Pp.primitive_tuple_pattern in
      let existential_typs_typ =
        typ_params |>
        List.map (fun (_, arity) -> Pp.typ_arity arity) |>
        Pp.primitive_tuple_type in
      nest (braces (
        existential_typs_pattern ^^ !^ ":" ^^ existential_typs_typ ^^ !^ "@" ^^
        to_coq subst None typ
      ))
  | ForallModule (name, param, result) ->
    Context.parens context Context.Forall @@ group (
      nest (
        !^ "forall" ^^ parens (
          Name.to_coq name ^^ !^ ":" ^^ to_coq subst None param
        ) ^-^ !^ ","
      ) ^^
      to_coq subst None result
    )
  | ForallTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ group (
        nest (
          !^ "forall" ^^ to_coq_grouped_typ_params Braces typ_args ^-^ !^ ","
        ) ^^
        to_coq subst None typ
      )
    end
  | FunTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "fun" ^^ parens (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^^ !^ "=>" ^^
        to_coq subst (Some Context.Forall) typ
      )
    end
  | Error message -> !^ message

let typ_vars_to_coq
    (delim : SmartPrint.t -> SmartPrint.t)
    (sep_before : SmartPrint.t)
    (sep_after : SmartPrint.t)
    (typ_vars : VarEnv.t) : SmartPrint.t =
  let typ_vars = VarEnv.group_by_kind typ_vars in
  if List.length typ_vars = 0
  then empty
  else nest (sep_before ^^
       (separate space
          (typ_vars |> List.map (fun (typ, vars) ->
               ((delim ((separate space (vars |> List.rev |> List.map Name.to_coq))
                      ^^ !^ ":" ^^ (Kind.to_coq typ)))))
          )) ^-^ sep_after)
