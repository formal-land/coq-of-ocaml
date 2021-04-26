open Typedtree
open SmartPrint
open Monad.Notations

module Inductive = struct
  type notation = Name.t * VarEnv.t * Type.t

  type t = {
    constructor_records
      : (Name.t * (AdtConstructors.RecordSkeleton.t * VarEnv.t * Type.t) list) list;
    notations : notation list;
    records : AdtConstructors.RecordSkeleton.t list;
    (* typs is a list of mutually defined Inductives
     * of the form
     * Inductive `Name.t` (`Name.t list` : Set) : Set :=
     * | `Constructor.t` ...
     * with `Name.t` (`Name.t list` : set) : Set := ...
     *)
    typs : (Name.t * Name.t list * AdtConstructors.t) list;
  }

  let get_notation_module_name (inductive : t) : SmartPrint.t =
    !^ "ConstructorRecords_" ^-^
    separate (!^ "_") (inductive.constructor_records |> List.map (fun (name, _) ->
      Name.to_coq name
    ))

  let to_coq_constructor_records (inductive : t) : SmartPrint.t option =
    match inductive.constructor_records with
    | [] -> None
    | constructor_records ->
      let notation_module_name = get_notation_module_name inductive in
      Some (
        !^ "(** Records for the constructor parameters *)" ^^ newline ^^
        !^ "Module" ^^ notation_module_name ^-^ !^ "." ^^ newline ^^
        indent (
          separate newline (
            constructor_records |> List.map (fun (name, records) ->
            !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
            indent (
              separate
                (newline ^^ newline)
                (records |> List.map (fun (record, _, _) ->
                  AdtConstructors.RecordSkeleton.to_coq record
                ))
            ) ^^ newline ^^
            !^ "End" ^^ Name.to_coq name ^-^ !^ "."
          ))
        ) ^^ newline ^^
        !^ "End" ^^ notation_module_name ^-^ !^ "." ^^ newline ^^
        !^ "Import" ^^ notation_module_name ^-^ !^ "."
      )

  let to_coq_notation_name (name : Name.t) : SmartPrint.t =
    !^ "\"'" ^-^ Name.to_coq name ^-^ !^ "\""

  let to_coq_notation_record (prefix : Name.t) (name : Name.t) : SmartPrint.t =
    !^ "\"'" ^-^ Name.to_coq prefix ^-^ !^ "." ^-^ Name.to_coq name ^-^ !^ "\""

  let to_coq_notations_reserved (inductive : t) : SmartPrint.t list =
    (inductive.constructor_records |> List.map
      (fun (name, records) ->
        records |> List.map (fun ({ AdtConstructors.RecordSkeleton.module_name; _ }, _, _) ->
          !^ "Reserved Notation" ^^ to_coq_notation_record name module_name ^-^
          !^ "."
        )
      )
      |> List.concat
    ) @
    (inductive.notations |> List.map (fun (name, _, _) ->
      !^ "Reserved Notation" ^^ to_coq_notation_name name ^-^ !^ "."
    ))

  let to_coq_record_skeletons (inductive : t) : SmartPrint.t list =
    inductive.records |> List.map AdtConstructors.RecordSkeleton.to_coq

  let to_coq_typs
    (subst : Type.Subst.t)
    (is_first : bool)
    (name : Name.t)
    (left_typ_args : Name.t list)
    (constructors : AdtConstructors.t)
    : SmartPrint.t =
    let keyword = if is_first then !^ "Inductive" else !^ "with" in
    nest (
      keyword ^^ Name.to_coq name ^^
      (if left_typ_args = [] then
        empty
      else
        parens (
          nest (
            separate space (left_typ_args |> List.map Name.to_coq) ^^
            !^ ":" ^^ Pp.set
          )
        )
     ) ^^ !^ ":" ^^
      let res_typ_length = match constructors with
        | [] -> 0
        | constructor :: _ -> match constructor.res_typ_params with
          | AdtConstructors.Variant l -> List.length l
          | Tagged l -> List.length l
      in
      let is_tagged = match constructors with
        | [] -> false
        | c :: _ -> c.is_tagged
      in

      let arity = if not is_tagged then 1 else res_typ_length + 1 in
      let index_typs = List.init arity (fun i ->
          if i = arity - 1
          then Pp.set
          else !^ "vtag")
      in
      separate (space ^^ !^ "->" ^^ space) index_typs
      ^^ !^ ":=" ^-^
      separate empty (
        constructors |> List.map (fun {
            AdtConstructors.constructor_name;
            param_typs;
            res_typ_params;
            typ_vars;
          } ->
          newline ^^ nest (
            !^ "|" ^^ Name.to_coq constructor_name ^^ !^ ":" ^^
            Type.typ_vars_to_coq braces (!^ "forall") (!^ ",") typ_vars ^^
            group @@ separate space (param_typs |> List.map (fun param_typ ->
              group (Type.to_coq (Some subst) (Some Type.Context.Arrow) param_typ ^^ !^ "->")
              )) ^^
                     let res_typ_params = match res_typ_params with
                       | Variant vars ->
                         let typs = vars |> AdtParameters.get_parameters |> List.map (fun var -> Type.Variable var) in
                         List.combine typs (Type.tag_no_args typs)
                       | Tagged typ_params ->
                         List.combine typ_params (Type.tag_all_args typ_params)
              in
              Type.to_coq (Some subst) None (Type.Apply (MixedPath.of_name name, res_typ_params))
          )
        )
      )
    )

  let to_coq_notations_where
    (subst : Type.Subst.t)
    (notation : SmartPrint.t)
    (typ_args : VarEnv.t)
    (typ : Type.t)
    : SmartPrint.t =
    let typ =
      List.fold_left (fun typ (typ_arg, _) ->
        Type.subst_name typ_arg (Name.prefix_by_t typ_arg) typ
      ) typ typ_args in
    let typ_args = typ_args |> List.map (fun (name, typ) -> (Name.prefix_by_t name, typ)) in
    nest (
      notation ^^ !^ ":=" ^^ parens (
        (match typ_args with
         | [] -> empty
         | _ :: _ -> Type.typ_vars_to_coq parens (!^ "fun") (!^" => ") typ_args
        )
        ^-^ Type.to_coq (Some subst) None typ
      )
    )

  let rec sort_notations (sorted : notation list) (to_sort : notation list)
    : notation list =
    let to_sort_names = List.map (fun (name, _, _) -> name) to_sort in
    let (selected, to_sort) =
      to_sort |> List.partition (fun (_, typ_args, typ) ->
        let dependencies =
          Name.Set.diff
            (Type.local_typ_constructors_of_typ typ)
            (Name.Set.of_list (List.map fst typ_args)) in
        not (dependencies |> Name.Set.exists (fun dependency ->
          List.mem dependency to_sort_names
        ))
      ) in
    match selected with
    | [] -> sorted @ to_sort
    | _ :: _ -> sort_notations (sorted @ selected) to_sort

  let to_coq_notations_wheres
    (subst : Type.Subst.t)
    (inductive : t)
    : SmartPrint.t list =
    let sorted_notations = sort_notations [] inductive.notations in
    (sorted_notations |> List.map (fun (name, typ_args, typ) ->
      to_coq_notations_where subst (to_coq_notation_name name) typ_args typ
    )) @
    (inductive.constructor_records |> List.map
      (fun (name, records) ->
        records |> List.map (fun ({ AdtConstructors.RecordSkeleton.module_name; _ }, typ_args, typ) ->
          to_coq_notations_where
            subst
            (to_coq_notation_record name module_name)
            typ_args
            typ
        )
      )
      |> List.concat
    )

  let to_coq_notations_definition (name : Name.t) (definition : SmartPrint.t)
    : SmartPrint.t =
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^ definition ^-^ !^ "."
    )

  let to_coq_notations_record_definitions (inductive : t) : SmartPrint.t option =
    match inductive.constructor_records with
    | [] -> None
    | _ :: _ ->
      let notation_module_name = get_notation_module_name inductive in
      Some (
        separate newline (inductive.constructor_records |> List.map (fun (name, records) ->
          !^ "Module" ^^ Name.to_coq name ^-^ !^ "." ^^ newline ^^
          indent (
            !^ "Include" ^^ notation_module_name ^-^ !^ "." ^-^
              Name.to_coq name ^-^ !^ "." ^^ newline ^^
            separate newline (records |> List.map
              (fun ({ AdtConstructors.RecordSkeleton.module_name; _ }, _, _) ->
                to_coq_notations_definition
                  module_name
                  (!^ "'" ^-^ Name.to_coq name ^-^ !^ "." ^-^ Name.to_coq module_name)
              )
            )
          ) ^^ newline ^^
          !^ "End" ^^ Name.to_coq name ^-^ !^ "."
        ))
      )

  let to_coq_notations_definitions (inductive : t) : SmartPrint.t list =
    inductive.notations |> List.map (fun (name, _, _) ->
      to_coq_notations_definition
        name
        (Name.to_coq (Name.prefix_by_single_quote name))
    )

  let to_coq_typs_implicits
    (left_typ_args : Name.t list)
    (constructors : AdtConstructors.t)
    : SmartPrint.t list =
    match left_typ_args with
    | [] -> []
    | _ :: _ ->
      constructors |> List.map (fun {
          AdtConstructors.constructor_name; typ_vars; _
        } ->
        !^ "Arguments" ^^ Name.to_coq constructor_name ^^ braces (
          nest (
            separate space (
              (left_typ_args |> List.map (fun _ -> !^ "_")) @
              (typ_vars |> List.map (fun _ -> !^ "_"))
            )
          )
        ) ^-^ !^ "."
      )


  let to_coq (inductive : t) : SmartPrint.t =
    let subst = {
      Type.Subst.path_name = (fun path_name ->
        match path_name with
        | { PathName.path = []; base } ->
          let use_notation =
            inductive.notations |> List.exists (fun (name, _, _) ->
              name = base
            ) in
          if use_notation then
            { path = []; base = Name.prefix_by_single_quote base }
          else
            path_name
        | { path = [prefix]; base } ->
          let use_notation =
            inductive.constructor_records |> List.exists (fun (name, records) ->
              records |> List.exists
                (fun ({ AdtConstructors.RecordSkeleton.module_name; _ }, _, _) ->
                  name = prefix && module_name = base
                )
            ) in
          if use_notation then
            { path = [Name.prefix_by_single_quote prefix]; base }
          else
            path_name
        | _ -> path_name)
    } in
    let constructor_records = to_coq_constructor_records inductive in
    let record_skeletons = to_coq_record_skeletons inductive in
    let reserved_notations = to_coq_notations_reserved inductive in
    let notations_wheres = to_coq_notations_wheres subst inductive in
    let notations_record_definitions = to_coq_notations_record_definitions inductive in
    let notations_definitions = to_coq_notations_definitions inductive in
    let implicit_arguments =
      List.concat (inductive.typs |> List.map (fun (_, left_typ_args, constructors) ->
        to_coq_typs_implicits left_typ_args constructors
      )) in
    nest (
      (match constructor_records with
      | None -> empty
      | Some constructor_records -> constructor_records ^^ newline ^^ newline) ^^
      (match record_skeletons with
      | [] -> empty
      | _ :: _ -> separate (newline ^^ newline) record_skeletons ^^ newline ^^ newline) ^^
      (match reserved_notations with
      | [] -> empty
      | _ :: _ -> separate newline reserved_notations ^^ newline ^^ newline) ^^
      separate (newline ^^ newline) (inductive.typs |>
        List.mapi (fun index (name, left_typ_args, constructors) ->
          let is_first = index = 0 in
          to_coq_typs subst is_first name left_typ_args constructors
        )
      ) ^-^
      (match notations_wheres with
      | [] -> empty
      | _ :: _ ->
        newline ^^ newline ^^
        !^ "where " ^-^ separate (newline ^^ !^ "and ") notations_wheres
      ) ^-^ !^ "." ^^
      (match notations_record_definitions with
      | None -> empty
      | Some notations -> newline ^^ newline ^^ notations) ^^
      (match notations_definitions with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline notations_definitions) ^^
      (match implicit_arguments with
      | [] -> empty
      | _ :: _ -> newline ^^ newline ^^ separate newline implicit_arguments)
    )
end

type t =
  | Inductive of Inductive.t
  | Record of Name.t * Name.t list * (Name.t * Type.t) list * bool
  | Synonym of Name.t * Name.t list * Type.t
  | ExtensibleTyp of Name.t
  | Abstract of Name.t * Name.t list

let filter_in_free_vars
  (typ_args : Name.t list) (free_vars : Name.Set.t) : Name.t list =
  typ_args |> Util.List.filter_map (function typ_arg ->
      if Name.Set.mem typ_arg free_vars then
        Some typ_arg
      else
        None
  )

let of_ocaml (typs : type_declaration list) : t Monad.t =
  match typs with
  | [ { typ_id; typ_type = { type_manifest = Some typ; type_params; _ }; _ } ] ->
    let* name = Name.of_ident false typ_id in
    AdtParameters.of_ocaml type_params >>= fun ind_vars ->
    let typ_args = AdtParameters.get_parameters ind_vars in
    begin match typ.Types.desc with
    | Tvariant { row_fields; _ } ->
      Monad.List.map
        (AdtConstructors.of_ocaml_row ind_vars)
        row_fields >>= fun single_constructors ->
      AdtConstructors.of_ocaml ind_vars single_constructors >>= fun (constructors, _) ->
      raise
        (Inductive {
          constructor_records = [];
          notations = [];
          records = [];
          typs = [(name, typ_args, constructors)];
        })
        NotSupported
        "Polymorphic variant types are defined as standard algebraic types"
    | _ ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      let free_vars = Type.typ_args_of_typ typ in
      let typ_args = filter_in_free_vars typ_args free_vars in
      return (Synonym (name, typ_args, typ))
    end
  | [ { typ_id; typ_type = { type_kind = Type_abstract; type_manifest = None; type_params; _ }; typ_attributes; _ } ] ->
    Attribute.of_attributes typ_attributes >>= fun typ_attributes ->
    let* name = Name.of_ident false typ_id in
    AdtParameters.of_ocaml type_params >>= fun typ_args ->
    let typ_args_with_unknowns =
      if not (Attribute.has_phantom typ_attributes) then
        AdtParameters.get_parameters typ_args
      else
        [] in
    return (Abstract (name, typ_args_with_unknowns))
  | [ { typ_id; typ_type = { type_kind = Type_record (fields, _); type_params; _ }; _ } ] ->
    let* name = Name.of_ident false typ_id in
    AdtParameters.of_ocaml type_params >>= fun typ_args ->
    (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
      let* x = Name.of_ident false x in
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (x, typ)
    )) >>= fun fields ->
    let free_vars = Type.typ_args_of_typs (List.map snd fields) in
    let typ_args = AdtParameters.get_parameters typ_args in
    let typ_args = filter_in_free_vars typ_args free_vars in
    return (Record (name, typ_args, fields, true))
  | [ { typ_id; typ_type = { type_kind = Type_open; _ }; _ } ] ->
    let* name = Name.of_ident false typ_id in
    return (ExtensibleTyp name)
  | _ ->
    (typs |> Monad.List.fold_left (fun (constructor_records, notations, records, typs) typ ->
      set_loc typ.typ_loc (
      let* name = Name.of_ident false typ.typ_id in
      AdtParameters.of_ocaml typ.typ_type.type_params >>= fun typ_args ->
      match typ with
      | { typ_type = { type_manifest = Some typ; _ }; _ } ->
        begin match typ.Types.desc with
        | Tvariant { row_fields; _ } ->
          Monad.List.map (AdtConstructors.of_ocaml_row typ_args) row_fields >>= fun single_constructors ->
          AdtConstructors.of_ocaml typ_args single_constructors >>= fun (constructors, _) ->
          raise
            (
              constructor_records,
              notations,
              records,
              (name, typ_args, constructors) :: typs
            )
            NotSupported
            "Polymorphic variant types are defined as standard algebraic types"
        | _ ->
          Type.of_typ_expr true Name.Map.empty typ >>= fun (typ, _, typ_args) ->
          let* typ = Type.decode_var_tags typ_args false typ in
          return (
            constructor_records,
            (
              name,
              typ_args,
              typ
            ) :: notations,
            records,
            typs
          )
        end
      | { typ_type = { type_kind = Type_abstract; type_manifest = None; _ }; _ } ->
        raise
          (constructor_records, notations, records, typs)
          NotSupported
          "Abstract types not supported in mutually recursive definitions"
      | { typ_type = { type_kind = Type_record (fields, _); type_params = params ;_ }; _ } ->
        (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ; _ } ->
          let* x = Name.of_ident false x in
          Type.of_typ_expr true Name.Map.empty typ >>= fun (typ, _, new_typ_args) ->
          return (x, typ, new_typ_args)
        )) >>= fun fields ->
        let* (_, _, typ_args) = Type.of_typs_exprs true params Name.Map.empty in
        let typ_args = List.map fst typ_args in
        let (fields_names, fields_types, new_typ_args) = Util.List.split3 fields in
        let new_typ_args = VarEnv.merge new_typ_args in
        let typ_args = VarEnv.reorg typ_args new_typ_args in
        let* fields_types = Monad.List.map (Type.decode_var_tags typ_args false) fields_types in
        return (
          constructor_records,
          (
            name,
            typ_args,
            Type.Apply (
              MixedPath.of_name (Name.suffix_by_skeleton name),
              List.combine fields_types (Type.tag_no_args fields_types)
            )
          ) :: notations,
          {
            AdtConstructors.RecordSkeleton.fields = fields_names;
            module_name = name;
            typ_name = Name.suffix_by_skeleton name;
           } :: records,
          typs
        )
      | { typ_type = { type_kind = Type_variant cases; _ }; typ_attributes; _ } ->
        let* attributes = Attribute.of_attributes typ_attributes in
        Monad.List.map (AdtConstructors.of_ocaml_case name attributes typ_args) cases >>= fun cases ->
        let (single_constructors, new_constructor_records) = List.split cases in
        let new_constructor_records =
          new_constructor_records |> Util.List.filter_map (fun x -> x) in
        let constructor_records =
          match new_constructor_records with
          | [] -> constructor_records
          | _ :: _ ->
            (name, new_constructor_records) :: constructor_records in
        AdtConstructors.of_ocaml typ_args single_constructors >>= fun (constructors, merged_typ_params) ->
        return (
          constructor_records,
          notations,
          records,
          (name, merged_typ_params, constructors) :: typs
        )
      | { typ_type = { type_kind = Type_open; _ }; _ } ->
        raise
          (constructor_records, notations, records, typs)
          ExtensibleType
          "We do not handle extensible types in mutually recursive definitions"
      )
    ) ([], [], [], [])) >>= fun (constructor_records, notations, records, typs) ->
    let typs = typs |> List.map (function (x, y, z) -> (x, AdtParameters.get_parameters y, z)) in
    return (
      Inductive {
        constructor_records = List.rev constructor_records;
        notations = List.rev notations;
        records;
        typs = List.rev typs
      }
    )

let to_coq (with_args : bool) (def : t) : SmartPrint.t =
  match def with
  | Inductive inductive -> Inductive.to_coq inductive
  | Record (name, typ_args, fields, with_with) ->
    AdtConstructors.RecordSkeleton.to_coq_record name name typ_args fields with_with
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      Pp.args with_args ^^
      begin match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ Pp.set)
      end ^^
      nest (!^ ":" ^^ Pp.set) ^^
      !^ ":=" ^^ Type.to_coq None None value ^-^ !^ "."
    )
  | ExtensibleTyp name ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^ !^ ":=" ^^ !^ "extensible_type" ^-^
      !^ "."
    )
  | Abstract (name, typ_args) ->
    nest (
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ parens (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ Pp.set)) ^-^ !^ ",") ^^
      Pp.set ^-^ !^ ".")
