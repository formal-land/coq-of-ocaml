open Sexplib.Std
open SmartPrint
open Typedtree

type defined_or_existential =
  | Defined of Type.t
  | Existential of Name.t
  [@@deriving sexp]

type t =
  | With of BoundName.t * defined_or_existential list
  [@@deriving sexp]

let of_ocaml_module_with_substitutions
  (env : FullEnvi.t)
  (loc :Loc.t)
  (long_ident_loc : Longident.t Asttypes.loc)
  (substitutions : (Path.t * Longident.t Asttypes.loc * with_constraint) list)
  : t =
  let name = Envi.bound_name loc (PathName.of_loc long_ident_loc) env.FullEnvi.signatures in
  let signature_typ_params = Envi.find name env.FullEnvi.signatures in
  let typ_substitutions: (Name.t * Type.t) list = substitutions |> List.map (function
    | (Path.Pident ident, _, with_constraint) ->
      begin match with_constraint with
      | Twith_type { typ_loc; typ_type } ->
        begin match typ_type with
        | { type_kind = Type_abstract; type_manifest = Some typ } ->
          (Name.of_ident ident, Type.of_type_expr env (Loc.of_location typ_loc) typ)
        | _ ->
          Error.raise loc (
            "Can only do `with` on types in module types using type expressions " ^
            "rather than type definitions."
          )
        end
      | _ -> Error.raise loc "Can only do `with` on types in module types."
      end
    | (_, _, _) -> Error.raise loc "Can only do `with` in module types for top-level identifiers."
  ) in
  let typ_values = List.fold_left
    (fun typ_values (name, typ) ->
      typ_values |> List.map (fun defined_or_existential ->
        match defined_or_existential with
        | Existential name' -> if name = name' then Defined typ else defined_or_existential
        | _ -> defined_or_existential
      )
    )
    (signature_typ_params |> List.map (fun name -> Existential name))
    typ_substitutions in
  With (name, typ_values)

let of_ocaml (env : FullEnvi.t) (module_typ : module_type) : t =
  let loc = Loc.of_location module_typ.mty_loc in
  match module_typ.mty_desc with
  | Tmty_alias _ -> Error.raise loc "Aliases in module types are not handled."
  | Tmty_functor _ -> Error.raise loc "The application of functors in module types is not handled."
  | Tmty_ident (_, long_ident_loc) ->
    of_ocaml_module_with_substitutions env loc long_ident_loc []
  | Tmty_signature signature ->
    Error.raise loc "Anonymous definition of signatures is not handled."
  | Tmty_typeof _ -> Error.raise loc "The typeof in module types is not handled."
  | Tmty_with ({ mty_desc = Tmty_ident (_, long_ident_loc) }, substitutions) ->
    of_ocaml_module_with_substitutions env loc long_ident_loc substitutions
  | Tmty_with _ ->
    Error.raise loc "With on something else than a signature name is not handled."

let to_coq (module_typ : t) : SmartPrint.t =
  match module_typ with
  | With (name, typ_values) ->
    let existential_names = List.fold_left
      (fun names defined_or_existential ->
        match defined_or_existential with
        | Defined _ -> names
        | Existential name -> name :: names
      )
      [] typ_values in
    braces (indent (
      begin match existential_names with
      | [] -> !^ "_" ^^ !^ ":" ^^ !^ "unit" ^^ !^ "&"
      | [existential_name] -> Name.to_coq existential_name ^^ !^ ":" ^^ !^ "Type" ^^ !^ "&"
      | _ ->
        !^ "existential_types" ^^ !^ ":" ^^
        separate (space ^^ !^ "*" ^^ space) (List.map (fun _ -> !^ "Type") existential_names) ^^
        !^ "&" ^^ !^ "let" ^^
        !^ "'(" ^-^ indent (
          separate (!^ "," ^^ space) (List.map Name.to_coq existential_names)
        ) ^-^ !^ ")" ^^
        !^ ":=" ^^ !^ "existential_types" ^^ !^ "in"
      end ^^
      BoundName.to_coq name ^^
      separate space (typ_values |> List.map (function
        | Defined typ -> Type.to_coq true typ
        | Existential name -> Name.to_coq name
      ))
    ))
