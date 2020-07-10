(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
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

(** [constructor_name]: forall [typ_vars], [param_typs] -> t [res_typ_params] *)
type item = {
  constructor_name : Name.t;
  param_typs : Type.t list; (** The parameters of the constructor. *)
  res_typ_params : Type.t list;
  (** The type parameters of the result type of the constructor. *)
  typ_vars : Name.t list; (** The polymorphic type variables. *)
}

type t = item list

module Single = struct
  type t = {
    constructor_name : Name.t;
    param_typs : Type.t list; (** The parameters of the constructor. *)
    return_typ_params : Type.t list;
    (** The return type, in case of GADT constructor, with some inference to
        rule-out GADTs with only existential variables. *)
  }

  let of_ocaml_case
      (typ_name : Name.t)
      (defined_typ_params : Name.t list)
      (case : Types.constructor_declaration)
    : (t * (RecordSkeleton.t * Name.t list * Type.t) option) Monad.t =
    let { Types.cd_args; cd_id; cd_loc; cd_res; _ } = case in
    set_loc (Loc.of_location cd_loc) (
      let* constructor_name =
        PathName.map_constructor_name
          (Ident.name cd_id) (Name.to_string typ_name) in
      let* constructor_name = Name.of_string false constructor_name in
      let typ_vars = Name.Map.empty in
      begin match cd_args with
        | Cstr_tuple param_typs ->
          Type.of_typs_exprs true typ_vars param_typs >>= fun (param_typs, _, _) ->
          return (param_typs, None)
        | Cstr_record labeled_typs ->
          set_loc (Loc.of_location cd_loc) (
            (
              labeled_typs |>
              List.map (fun { Types.ld_type; _ } -> ld_type) |>
              Type.of_typs_exprs true typ_vars
            ) >>= fun (record_params, _, _) ->
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
            return (
              [
                Type.Apply (
                  MixedPath.PathName {
                    path = [typ_name];
                    base = constructor_name;
                  },
                  typ_args |> List.map (fun name ->
                      Type.Variable name
                    )
                )
              ],
              Some (
                {
                  RecordSkeleton.fields = record_fields;
                  module_name = constructor_name;
                  typ_name = Name.suffix_by_skeleton constructor_name;
                },
                typ_args,
                Type.Apply (
                  MixedPath.PathName {
                    path = [typ_name];
                    base = Name.suffix_by_skeleton constructor_name;
                  },
                  record_params
                )
              )
            ))
      end >>= fun (param_typs, records) ->
      let* return_typ_params =
        match cd_res with
        | Some typ -> Type.of_typ_expr false Name.Map.empty typ >>= fun (ty, _, _) ->
          begin match ty with
            | Type.Apply (_, typs) -> return typs
            | _ -> raise [ty] Error.Category.Unexpected "Unexpected Type of record"
          end
        | None -> return (List.map (fun v -> Type.Variable v) defined_typ_params)
      in

      return (
        {
          constructor_name;
          param_typs;
          return_typ_params;
        },
        records
      ))

  let of_ocaml_row
      (defined_typ_params : AdtParameters.t)
      (row : Asttypes.label * Types.row_field)
    : t Monad.t =
    let (label, field) = row in
    let* constructor_name = Name.of_string false label in
    let typs = Type.type_exprs_of_row_field field in
    Type.of_typs_exprs true Name.Map.empty typs >>= fun (param_typs, _, _) ->
    return {
      constructor_name;
      param_typs;
      return_typ_params = List.map (fun x -> Type.Variable x) (AdtParameters.get_parameters defined_typ_params);
    }
end

let of_ocaml
    (single_constructors : Single.t list)
  : t Monad.t =

  let* constructors_and_arities  = single_constructors |> Monad.List.map (
      fun { Single.constructor_name; param_typs; return_typ_params } ->
        let typ_vars = param_typs |> Type.typ_args_of_typs in
        let typ_vars = return_typ_params |> Type.typ_args_of_typs |> Name.Set.union typ_vars |> Name.Set.elements in
        return ({
            constructor_name;
            param_typs;
            res_typ_params = return_typ_params;
            typ_vars
          }, List.length return_typ_params)
    ) in

  let (constructors, constructors_arity) = List.split constructors_and_arities in
  let same_arities = List.for_all (fun y -> List.hd constructors_arity = y) constructors_arity in

  if not same_arities
  then
    raise constructors
      Error.Category.Unexpected
      "Unexpected error made the constructors have different return sizes"
  else
    return constructors

let type_arguments
  (constructors : t)
  : Type.t list =
  constructors |> List.map (fun { res_typ_params; _ } ->
            res_typ_params) |> List.flatten

let from_tags (tags : Type.tags) : Name.t * Type.t list * t =
  let { Type.name; constructors } = tags in
  let constructors : (Type.t * Name.t) list = Type.Map.bindings constructors in
  let (typs, items) = constructors |> List.map (fun (typ, name) ->
      (typ,
       let param_typs = Type.typ_args_of_typ typ |> Name.Set.elements |>
           List.map (fun typ -> Type.SetTyp) in
       { constructor_name = name;
        param_typs ;
        res_typ_params = [];
        typ_vars = []
       })) |> List.split in
    (name, typs, items)
