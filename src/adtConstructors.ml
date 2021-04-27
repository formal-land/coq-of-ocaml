open SmartPrint
open Monad.Notations

module RecordSkeleton = struct
  type t = {
    fields : Name.t list;
    module_name : Name.t;
    typ_name : Name.t;
  }

  let to_coq_record
      (module_name : Name.t)
      (typ_name : Name.t)
      (typ_args : Name.t list)
      (fields : (Name.t * Type.t) list)
      (with_with : bool)
    : SmartPrint.t =
    nest (
      !^ "Module" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
      indent (
        !^ "Record" ^^ !^ "record" ^^
        begin match typ_args with
          | [] -> empty
          | _ :: _ ->
            braces (nest (
                separate space (List.map Name.to_coq typ_args) ^^
                !^ ":" ^^ Pp.set
              ))
        end ^^
        nest (!^ ":" ^^ Pp.set) ^^
        !^ ":=" ^^ !^ "Build" ^^
        !^ "{" ^^ newline ^^
        indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
            nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq None None typ)))) ^^
        !^ "}." ^^
        begin match typ_args with
          | [] -> empty
          | _ :: _ ->
            newline ^^ !^ "Arguments" ^^ !^ "record" ^^ !^ ":" ^^
            !^ "clear" ^^ !^ "implicits" ^-^ !^ "."
        end ^^
        newline ^^
        begin if with_with then
            separate newline (fields |> List.map (fun (name, _) ->
                let prefixed_typ_args =
                  typ_args |> List.map (fun typ_arg ->
                      Name.to_coq (Name.prefix_by_t typ_arg)
                    ) in
                let record_typ =
                  nest (separate space (!^ "record" :: prefixed_typ_args)) in
                nest (
                  !^ "Definition" ^^ Name.to_coq (Name.prefix_by_with name) ^^
                  begin match typ_args with
                    | [] -> empty
                    | _ :: _ -> braces (nest (separate space prefixed_typ_args))
                  end ^^
                  Name.to_coq name ^^
                  nest (parens (!^ "r" ^^ !^ ":" ^^ record_typ)) ^-^
                  !^ " :=" ^^ newline ^^
                  indent @@ nest (
                    !^ "Build" ^^
                    separate space prefixed_typ_args ^^
                    separate space (fields |> List.map (fun (name', _) ->
                        nest (
                          if Name.equal name name' then
                            Name.to_coq name
                          else
                            !^ "r" ^-^ !^ ".(" ^-^ Name.to_coq name' ^-^ !^ ")"
                        )
                      )) ^-^ !^ "."
                  )
                )
              )) ^^ newline
          else
            empty
        end
      ) ^^
      !^ "End" ^^ Name.to_coq module_name ^-^ !^ "." ^^ newline ^^
      nest (
        !^ "Definition" ^^ Name.to_coq typ_name ^^ !^ ":=" ^^
        Name.to_coq module_name ^-^ !^ ".record" ^-^ !^ "."
      )
    )


  let to_coq (record_skeleton : t) : SmartPrint.t =
    let { fields; module_name; typ_name } = record_skeleton in
    to_coq_record module_name typ_name fields (fields |>
                                               List.map (fun field -> (field, Type.Variable field))
                                              ) true
end

type ret_typ =
  | Variant of AdtParameters.t
  | Tagged of Type.t list

let ret_is_tagged : ret_typ -> bool = function
  | Variant _ -> false
  | Tagged _ -> true

(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
(** [constructor_name]: forall [typ_vars], [param_typs] -> t [res_typ_params] *)
type item = {
  constructor_name : Name.t;
  param_typs : Type.t list; (** The parameters of the constructor. *)
  res_typ_params : ret_typ;
  is_tagged : bool;
  (** The type parameters of the result type of the constructor. *)
  typ_vars : VarEnv.t; (** The polymorphic type variables. *)
}

type t = item list

let of_ocaml_case
    (typ_name : Name.t)
    (attributes : Attribute.t list)
    (defined_typ_params : AdtParameters.t)
    (case : Types.constructor_declaration)
  : (item * (RecordSkeleton.t * VarEnv.t * Type.t) option) Monad.t =
  let { Types.cd_args; cd_id; cd_loc; cd_res; cd_attributes } = case in
  set_loc cd_loc (
    let* constructor_name =
      PathName.map_constructor_name
        (Ident.name cd_id) (Name.to_string typ_name) in
    let* constructor_name = Name.of_string false constructor_name in
    let typ_vars = Name.Map.empty in
    begin match cd_args with
      | Cstr_tuple param_typs ->
        Type.of_typs_exprs true param_typs typ_vars >>= fun (param_typs, _, new_typ_vars) ->
        return (param_typs, new_typ_vars, None)
      | Cstr_record labeled_typs ->
        set_loc cd_loc (
          (
            labeled_typs |>
            List.map (fun { Types.ld_type; _ } -> ld_type) |>
            (fun ls -> Type.of_typs_exprs true ls typ_vars)
          ) >>= fun (record_params, _, new_typ_vars) ->
          let* record_fields =
            labeled_typs |> Monad.List.map ( fun { Types.ld_id; _ } ->
                Name.of_ident false ld_id
              ) in
          (* We get the order of the type arguments from their order of
             introduction in the record fields. *)
          let typ_args =
            List.fold_left
              (fun typ_args new_typ_args ->
                 (typ_args @
                  Name.Set.elements (
                    Name.Set.diff new_typ_args (Name.Set.of_list typ_args)
                  ))
              )
              []
              (List.map Type.typ_args_of_typ record_params) in
          let new_typ_vars = VarEnv.reorg typ_args new_typ_vars in
          let tag_typs = List.map (fun (_, kind) ->
              match kind with
              | Kind.Tag -> true
              | _ -> false
            ) new_typ_vars in
          let typ_args = new_typ_vars |> List.map (fun (name, _) ->
              Type.Variable name
            ) in
          return (
            [
              Type.Apply (
                MixedPath.PathName {
                  path = [typ_name];
                  base = constructor_name;
                },
                List.combine typ_args tag_typs
              )
            ],
            new_typ_vars,
            Some (
              {
                RecordSkeleton.fields = record_fields;
                module_name = constructor_name;
                typ_name = Name.suffix_by_skeleton constructor_name;
              },
              new_typ_vars,
              Type.Apply (
                MixedPath.PathName {
                  path = [typ_name];
                  base = Name.suffix_by_skeleton constructor_name;
                },
                List.combine record_params (Type.tag_no_args record_params)
              )
            )
          ))
    end >>= fun (param_typs, typ_vars, records) ->
    let is_tagged = Attribute.has_tag_gadt attributes in
    let is_gadt = Attribute.has_force_gadt attributes in
    let* (tagged_return, new_typ_vars) =
      match cd_res with
      | Some typ ->
        Type.of_typ_expr true Name.Map.empty typ >>= fun (ty, _, new_typ_vars) ->
        begin match ty with
          | Type.Apply (_, typs) ->
            let typs = List.map (fun t -> fst t) typs in
            return (typs, new_typ_vars)
          | _ -> raise ([ty], new_typ_vars) Error.Category.Unexpected "Unexpected Type of Constructor"
        end
      | None ->
        let kind = if is_tagged then Kind.Tag else Kind.Set in
        let typ_args = AdtParameters.get_parameters defined_typ_params in
        let new_typ_vars = List.fold_left (fun map typ_param ->
            (typ_param, kind) :: map
          ) [] typ_args in
        return ((List.map (fun v -> Type.Variable v) typ_args), List.rev new_typ_vars)
    in
    let typ_vars = VarEnv.union typ_vars new_typ_vars in
    let* param_typs = Monad.List.map (Type.decode_var_tags typ_vars false) param_typs in
    let* tagged_return = Monad.List.map (Type.decode_var_tags typ_vars true) tagged_return in
    let* untagged_return =
      AdtParameters.get_return_typ_params defined_typ_params cd_res in
    let res_typ_params = if is_tagged
      then Tagged(tagged_return)
      else if is_gadt
        then Variant []
        else Variant untagged_return in

    return (
      {
        constructor_name;
        param_typs;
        res_typ_params;
        is_tagged;
        typ_vars;
      },
      records
    ))

let of_ocaml_row
    (defined_typ_params : AdtParameters.t)
    (row : Asttypes.label * Types.row_field)
  : item Monad.t =
  let (label, field) = row in
  let* constructor_name = Name.of_string false label in
  let typs = Type.type_exprs_of_row_field field in
  Type.of_typs_exprs true typs Name.Map.empty >>= fun (param_typs, _, typ_vars) ->
  return {
    constructor_name;
    param_typs;
    res_typ_params =  Variant(defined_typ_params);
    is_tagged = false;
    typ_vars;
  }

let of_ocaml
    (defined_typ_params : AdtParameters.t)
    (single_constructors : t)
  : (t * AdtParameters.t) Monad.t =
  let length_and_return_typ = single_constructors |> List.map (
      fun {res_typ_params; _; } ->
        match res_typ_params with
          | Variant ls -> (List.length ls, ls)
          | Tagged ls -> (List.length ls, [])
    )
  in

  let (constructors_arity, constructors_return_typ_params) = List.split length_and_return_typ in
  let same_arities = List.for_all (fun y -> List.hd constructors_arity = y) constructors_arity in

  let merged_typ_params = AdtParameters.check_if_not_gadt
      defined_typ_params
      constructors_return_typ_params in

  let typ_params =
    match merged_typ_params with
    | None -> defined_typ_params
    | Some merged_typ_params -> merged_typ_params in

  let* constructors : t = single_constructors |> Monad.List.map (
      fun { constructor_name; param_typs; res_typ_params; typ_vars; _ } ->
        let (is_tagged, return_typ_params, return_len) = match res_typ_params with
          | Tagged ls -> (true, Tagged ls, List.length ls)
          | Variant ls -> (false, Variant typ_params, List.length ls)
        in

        let rem_names = param_typs |> Type.typ_args_of_typs in
        let non_params = typ_params |> AdtParameters.get_parameters |>
                          Name.Set.of_list |> Name.Set.diff rem_names |> Name.Set.elements in
        let typ_vars = if is_tagged
          then typ_vars
          else VarEnv.keep_only non_params typ_vars in

        return {
          constructor_name;
          param_typs;
          res_typ_params = return_typ_params;
          is_tagged;
          typ_vars;
        }
    ) in

  if not same_arities
  then
    raise (constructors, defined_typ_params)
      Error.Category.Unexpected
      "Unexpected error made the constructors have different return sizes"
  else
    return (constructors, typ_params)
