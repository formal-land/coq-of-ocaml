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
  | Apply of MixedPath.t * t list * bool list
  | Package of bool * PathName.t * arity_or_typ Tree.t
  | ForallModule of Name.t * t * t
  | ForallTyps of Name.t list * t
  | String of string
  | FunTyps of Name.t list * t
  | Error of string

and arity_or_typ =
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
  | Apply (mpath, _, _) -> MixedPath.to_string mpath
  | Package _ -> "package"
  | ForallModule _ -> "forallModule"
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
    return (Apply (tag, [t1; t2], [false; false]))
  | Tuple ts ->
    let tag = Name.tuple_tag |> MixedPath.of_name  in
    let bs = [false; false] in
    if List.length ts = 2
    then
      let* ts = Monad.List.map tag_ty ts in
      return (Apply (tag, ts, bs))
    else
      let* t = tag_ty (List.hd ts) in
      let* ts = tag_ty @@ Tuple (List.tl ts) in
      return (Apply (tag, [t; ts], bs))
  | Apply (mpath, ts, bs) ->
    let* ts = Monad.List.map tag_ty ts in
    let arg_names = List.map tag_constructor_of ts in
    let tag = Name.constr_tag |> MixedPath.of_name  in
    let name = (MixedPath.to_string mpath) in
    let str_repr = name ^
                   (List.fold_left (fun acc ty -> acc ^ "_" ^ ty) "" arg_names) in
    return (Apply (tag, [String str_repr; typ], [false; false]))
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
    | Apply (constructor, typs, bs) ->
        let constructor_with_subst =
          match constructor with
          | PathName { path = []; base } when Name.equal base source ->
            MixedPath.PathName { path = []; base = target }
          | _ -> constructor in
      Apply (constructor_with_subst, List.map subst typs, bs)
    | Package (is_in_exp, path_name, typ_params) ->
      Package (
        is_in_exp,
        path_name,
        typ_params |> Tree.map (fun arity_or_typ ->
          match arity_or_typ with
          | Arity _ -> arity_or_typ
          | Typ typ -> Typ (subst typ)
        )
      )
    | ForallModule (name, typ1, typ2) ->
      ForallModule (name, subst typ1, subst typ2)
    | ForallTyps (names, typ) ->
      ForallTyps (names, subst_after_names names typ)
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
            _, b
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
            typs, bs
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
            typs, bs
          )
        )
      | None -> None
      end
    | _ -> None in
  match apply_with_merge with
  | None -> return (Apply (mixed_path, typs, tag_list))
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
      let _ = Path.to_string_list path in
      MixedPath.of_path false path
    with _ -> return mixed_path
    end
  | _ -> return mixed_path


let is_native_type
    (typ : t)
  : bool =
  match typ with
  | Variable var -> List.mem (Name.to_string var) Name.native_types
  | Apply (mpath, _, _) -> MixedPath.is_native_type mpath
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
  | Apply (t, args, bs) ->
    let (args, eqs) = args |> List.mapi (fun i typ ->
        let x = "t" ^ string_of_int i |> Name.of_string_raw in
        (Variable x, Eq (Variable x, typ))
      ) |> List.split in
    (Apply (t, args, bs), eqs)
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
let rec of_typ_expr'
  (should_tag : bool)
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
        (typ_vars, [], name)
      ) else (
        let typ_vars = Name.Map.add source_name generated_name typ_vars in
        (typ_vars, [(generated_name, typ)], generated_name)
      ) in
    return (Variable name, typ_vars, new_typ_vars)
  | Tarrow (_, typ_x, typ_y, _) ->
    of_typ_expr' should_tag with_free_vars typ_vars typ_x >>= fun (typ_x, typ_vars, new_typ_vars_x) ->
    of_typ_expr' should_tag with_free_vars typ_vars typ_y >>= fun (typ_y, typ_vars, new_typ_vars_y) ->
    let new_typ_vars = VarEnv.union new_typ_vars_x new_typ_vars_y in
    return (Arrow (typ_x, typ_y), typ_vars, new_typ_vars)
  | Ttuple typs ->
    let tag_list = tag_args_with should_tag typs in
    of_typs_exprs' tag_list with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
    return (Tuple typs, typ_vars, new_typ_vars)
  | Tconstr (path, typs, _) ->
    non_phantom_typs path typs >>= fun typs ->
    (* TODO: Implement tagging *)
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
      let* (typs, typ_vars, new_typs_vars) = of_typs_exprs' tag_list with_free_vars typ_vars typs in
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
      let* (typs, typ_vars, new_typs_vars) = of_typs_exprs' tag_list with_free_vars typ_vars typs in
      let* typs = tag_typ_constr path typs in
      let* typ = apply_with_notations mixed_path typs tag_list in
      return (typ, typ_vars, new_typs_vars)

  | Tobject (_, object_descr) ->
    begin match !object_descr with
    | Some (path, _ :: typs) ->
      let tag_list = tag_args_with should_tag typs in
      let* are_tags = get_constr_arg_tags path in
      of_typs_exprs' tag_list with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars) ->
      MixedPath.of_path false path >>= fun mixed_path ->
      return (Apply (mixed_path, typs, are_tags), typ_vars, new_typ_vars)
    | _ ->
      raise
        (Error "unhandled_object_type", typ_vars, [])
        NotSupported
        "We do not handle this form of object types"
    end
  | Tfield (_, _, typ1, typ2) ->
    of_typ_expr' should_tag with_free_vars typ_vars typ1 >>= fun (typ1, typ_vars, new_typ_vars1) ->
    of_typ_expr' should_tag with_free_vars typ_vars typ2 >>= fun (typ2, typ_vars, new_typ_vars2) ->
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
  | Tlink typ | Tsubst typ -> of_typ_expr' should_tag with_free_vars typ_vars typ
  | Tvariant { row_fields; _ } ->
    PathName.typ_of_variants (List.map fst row_fields) >>= fun path_name ->
    begin match path_name with
    | Some path_name ->
      return (
        Apply (MixedPath.PathName path_name, [], []),
        typ_vars,
        []
      )
    | None ->
      Monad.List.fold_left
        (fun (fields, typ_vars, new_typ_vars) (name, row_field) ->
          let typs = type_exprs_of_row_field row_field in
          let tag_list = tag_args_with should_tag typs in
          of_typs_exprs' tag_list with_free_vars typ_vars typs >>= fun (typs, typ_vars, new_typ_vars') ->
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
    let typ_args = typ_args |> List.filter (fun typ_arg ->
      Name.Set.mem typ_arg non_phantom_vars
    ) in
    of_typ_expr' should_tag with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars_typ) ->
    let non_phantom_vars = Name.Set.elements non_phantom_vars in
    let new_typ_vars_typ = VarEnv.remove_many non_phantom_vars new_typ_vars_typ in
    return (ForallTyps (typ_args, typ), typ_vars, new_typ_vars_typ)
  | Tpackage (path, idents, typs) ->
      let* path_name = PathName.of_path_without_convert false path in
      let typ_substitutions = List.map2 (fun ident typ -> (ident, typ)) idents typs in
      Monad.List.fold_left
        (fun (typ_substitutions, typ_vars, new_typ_vars) (ident, typ) ->
          let* path_name = PathName.of_long_ident false ident in
          (* TODO: Why is this true?? *)
          of_typ_expr' true with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
          return (
            (path_name, typ) :: typ_substitutions,
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
        (fun typ_values (path_name, typ) ->
          Tree.map_at typ_values path_name (fun _ -> Typ typ)
        )
        (signature_typ_params |> Tree.map (fun arity -> Arity arity))
        typ_substitutions in
      return (Package (true, path_name, typ_params), typ_vars, new_typ_vars)

and of_typs_exprs'
    (tag_list : bool list)
    (with_free_vars: bool)
    (typ_vars : Name.t Name.Map.t)
    (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * VarEnv.t) Monad.t =
  if List.length tag_list <> List.length typs
  then raise ([], typ_vars, []) Error.Category.Unexpected "Calling of_typs_exprs_constr with tag_list of different size of typs (they should have the same size)"
  else
    let tag_typs = List.combine typs tag_list in
    (Monad.List.fold_left
       (fun (typs, typ_vars, new_typ_vars) (typ, should_tag) ->
          of_typ_expr' should_tag with_free_vars typ_vars typ >>= fun (typ, typ_vars, new_typ_vars') ->
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
  | { type_kind = Type_record _; type_params = params; _} ->
    (* TODO: Recursively check if record type should be a tag *)
    return @@ tag_no_args params
  | { type_manifest = None; type_kind = Type_abstract; type_params = params; _ } ->
    return @@ tag_no_args params
  | { type_manifest = Some typ; type_params = params; _ } ->
    let* (typ, typ_vars, new_typ_vars) = of_typ_expr' false true Name.Map.empty typ in
    return @@ List.map (fun (_, kind) ->
        match kind with
        | Kind.Tag -> true
        | _ -> false
      ) new_typ_vars
  (* TODO: Preserve order of type parameters *)
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

let of_typ_expr
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typ : Types.type_expr)
  : (t * Name.t Name.Map.t * VarEnv.t) Monad.t =
  of_typ_expr' false with_free_vars typ_vars typ

let of_typs_exprs
  (with_free_vars: bool)
  (typ_vars : Name.t Name.Map.t)
  (typs : Types.type_expr list)
  : (t list * Name.t Name.Map.t * VarEnv.t) Monad.t =
  let tag_list = tag_no_args typs in
  of_typs_exprs' tag_list with_free_vars typ_vars typs

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
      if not is_tag || in_native
      then return typ
      else match List.assoc_opt name typ_vars with
        | None -> return typ
        | Some Kind.Tag -> return @@ Apply (MixedPath.dec_name, [typ], [true])
        | Some _ -> return typ
    end
  | Arrow (t1, t2) ->
    let* t1 = decode_var_tags_aux typ_vars in_native true t1 in
    let* t2 = decode_var_tags_aux typ_vars in_native true t2 in
    return @@ Arrow (t1, t2)
  | Tuple ts ->
    let* ts = Monad.List.map (decode_var_tags_aux typ_vars in_native true) ts in
    return @@ Tuple ts
  | Apply (mpath, ts, bs) ->
    let path_str = MixedPath.to_string mpath in
    let in_native = List.mem path_str ["tuple_tag"; "arrow_tag"; "list_tag"; "option_tag"] in
    let dec = decode_var_tags_aux typ_vars in_native in
    let ts = List.combine ts bs in
    let* ts = Monad.List.map (fun (t, b) -> dec b t) ts in
    return @@ Apply (mpath, ts, bs)
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
  match typ with
  | Variable x -> Name.Set.singleton x
  | Arrow (typ1, typ2) | Eq (typ1, typ2) -> typ_args_of_typs [typ1; typ2]
  | Sum typs -> typ_args_of_typs (List.map snd typs)
  | Tuple typs | Apply (_, typs, _) -> typ_args_of_typs typs
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (typ_args_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    Name.Set.union (typ_args_of_typ param) (typ_args_of_typ result)
  | ForallTyps (typ_params, typ) | FunTyps (typ_params, typ) ->
    Name.Set.diff (typ_args_of_typ typ) (Name.Set.of_list typ_params)
  | _ -> Name.Set.empty

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
  | Apply (mixed_path, typs, _) ->
    let local_typ_constructors = local_typ_constructors_of_typs typs in
    begin match mixed_path with
    | MixedPath.PathName { path = []; base } ->
      Name.Set.add base local_typ_constructors
    | _ -> local_typ_constructors
    end
  | Package (_, _, typ_params) ->
    Tree.flatten typ_params |>
    Util.List.filter_map (fun (_, typ) ->
      match typ with
      | Arity _ -> None
      | Typ typ -> Some (local_typ_constructors_of_typ typ)
    ) |>
    List.fold_left Name.Set.union Name.Set.empty
  | ForallModule (_, param, result) ->
    local_typ_constructors_of_typs [param; result]
  | ForallTyps (_, typ) | FunTyps (_, typ) -> local_typ_constructors_of_typ typ
  | _ -> Name.Set.empty

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
      | Apply (mname, ts, bs) ->
        if List.mem name Name.native_type_constructors
        then Some (Apply (MixedPath.of_name tagged_name, ts, bs))
        else None
      | _ -> None

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
  | Apply (path, typs, _) ->
    (* Prints tags as notations *)
    let tag = tag_notation path typs in
    if Option.is_some tag
    then let tag = Option.get tag in
      to_coq subst (Some Context.Apply) tag
    else
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
  | Package (is_in_exp, path_name, typ_params) ->
    let existential_typs =
      Tree.flatten typ_params |>
      Util.List.filter_map (function
        | (path_name, Arity arity) -> Some (path_name, arity)
        | _ -> None
      ) in
    let existential_typs_pattern =
      existential_typs |>
      List.map (fun (path_name, _) ->
        ModuleTypParams.to_coq_typ_param_name path_name
      ) |>
      Pp.primitive_tuple_pattern in
    let existential_typs_typ =
      existential_typs |>
      List.map (fun (_, arity) -> Pp.typ_arity arity) |>
      Pp.primitive_tuple_type in
    nest (braces (
      existential_typs_pattern ^^ !^ ":" ^^ existential_typs_typ ^^
      (if is_in_exp then !^ "@" else !^ "&") ^^
      nest (
        separate space (
          nest (PathName.to_coq path_name ^-^ !^ "." ^-^ !^ "signature") ::
          (Tree.flatten typ_params |> List.map (fun (path_name, typ) ->
            let name = ModuleTypParams.to_coq_typ_param_name path_name in
            nest (parens (
              name ^^ !^ ":=" ^^
              match typ with
              | Arity _ -> name
              | Typ typ -> to_coq subst (Some Context.Apply) typ
            ))
          ))
        )
      )
    ))
  | ForallModule (name, param, result) ->
    Context.parens context Context.Forall @@ nest (
      !^ "forall" ^^ parens (
        Name.to_coq name ^^ !^ ":" ^^ to_coq subst None param
      ) ^-^ !^ "," ^^
      to_coq subst (Some Context.Forall) result
    )
  | ForallTyps (typ_args, typ) ->
    begin match typ_args with
    | [] -> to_coq subst context typ
    | _ :: _ ->
      Context.parens context Context.Forall @@ nest (
        !^ "forall" ^^ braces (
          nest (
            separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set
          )
        ) ^-^ !^ "," ^^
        to_coq subst (Some Context.Forall) typ
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
  else sep_before ^^
       (separate space
          (typ_vars |> List.map (fun (typ, vars) ->
               delim ((separate space (vars |> List.rev |> List.map Name.to_coq))
                      ^^ !^ ":" ^^ (Kind.to_coq typ)))
       )) ^-^ sep_after
