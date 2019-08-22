open Typedtree
open Sexplib.Std
open SmartPrint

(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
module Constructors = struct
  type t =
    | Gadt of (Name.t * Name.t list * Type.t list * Type.t) list
    | NonGadt of (Name.t * Type.t list) list
    [@@deriving sexp]

  let rec of_ocaml (env : FullEnvi.t) (defined_typ : Type.t)
    (cases : Types.constructor_declaration list) : t =
    match cases with
    | [] -> NonGadt []
    | { cd_args; cd_id; cd_loc; cd_res; } :: cases ->
      let name = Name.of_ident cd_id in
      let loc = Loc.of_location cd_loc in
      let typs =
        match cd_args with
        | Cstr_tuple typs -> List.map (fun typ -> Type.of_type_expr env loc typ) typs
        | Cstr_record _ ->
          let loc = Loc.of_location cd_loc in
          Error.raise loc "Unhandled named constructor parameters." in
      let res_typ =
        match cd_res with
        | None -> None
        | Some res -> Some (Type.of_type_expr env loc res) in
      let res_typ_or_defined_typ =
        match res_typ with
        | None -> defined_typ
        | Some res_typ -> res_typ in
      (* We need to compute the free variables to add `forall` annotations in Coq as
         polymorphic variables cannot be infered. *)
      let free_typ_vars = Name.Set.elements (Type.typ_args_of_typs (res_typ_or_defined_typ :: typs)) in
      let constructors = of_ocaml env defined_typ cases in
      (* In case of types mixing GADT and non-GADT constructors, we automatically lift
         to a GADT type. *)
      match (res_typ, constructors) with
      | (None, NonGadt constructors) ->
        NonGadt ((name, typs) :: constructors)
      | (Some res_typ, Gadt constructors) ->
        Gadt ((name, free_typ_vars, typs, res_typ) :: constructors)
      | (None, Gadt constructors) ->
        Gadt ((name, free_typ_vars, typs, defined_typ) :: constructors)
      | (Some res_typ, NonGadt constructors) ->
        let lifted_constructors = constructors |> List.map (fun (name, typs) ->
          let free_typ_vars = Name.Set.elements (Type.typ_args_of_typs (defined_typ :: typs)) in
          (name, free_typ_vars, typs, defined_typ)
        ) in
        Gadt ((name, free_typ_vars, typs, res_typ) :: lifted_constructors)

  let constructor_names (constructors : t) : Name.t list =
    match constructors with
    | Gadt cases -> List.map (fun (x, _, _, _) -> x) cases
    | NonGadt cases -> List.map (fun (x, _) -> x) cases
end

type t =
  | Inductive of Name.t * Name.t list * Constructors.t
  | Record of Name.t * (Name.t * Type.t) list
  | Synonym of Name.t * Name.t list * Type.t
  | Abstract of Name.t * Name.t list
  [@@deriving sexp]

let of_ocaml (env : FullEnvi.t) (loc : Loc.t) (typs : type_declaration list) : t =
  match typs with
  | [] -> Error.raise loc "Unexpected type definition with no case."
  | [ { typ_id; typ_type } ] ->
    let name = Name.of_ident typ_id in
    let env = FullEnvi.add_typ [] name env in
    let typ_args =
      List.map (Type.of_type_expr_variable loc) typ_type.type_params in
    (match typ_type.type_kind with
    | Type_variant cases ->
      (* The `defined_typ` is useful to give a default return type for non-GADT
         constructors in GADT types. *)
      let defined_typ = Type.Apply (
        Envi.bound_name loc (PathName.of_name [] name) env.FullEnvi.typs,
        List.map (fun typ_arg -> Type.Variable typ_arg) typ_args
      ) in
      let constructors = Constructors.of_ocaml env defined_typ cases in
      Inductive (name, typ_args, constructors)
    | Type_record (fields, _) ->
      let fields =
        fields |> List.map (fun { Types.ld_id = x; ld_type = typ } ->
          (Name.of_ident x, Type.of_type_expr env loc typ)) in
      Record (name, fields)
    | Type_abstract ->
      (match typ_type.type_manifest with
      | Some typ -> Synonym (name, typ_args, Type.of_type_expr env loc typ)
      | None -> Abstract (name, typ_args))
      | Type_open -> Error.raise loc "Open type definition not handled.")
  | typ :: _ :: _ -> Error.raise loc "Type definition with 'and' not handled."

let update_env (def : t) (env : FullEnvi.t) : FullEnvi.t =
  match def with
  | Inductive (name, _, constructors) ->
    let env = FullEnvi.add_typ [] name env in
    let constructor_names = Constructors.constructor_names constructors in
    List.fold_left (fun env name -> FullEnvi.add_constructor [] name env) env constructor_names
  | Record (name, fields) ->
    let env = FullEnvi.add_typ [] name env in
    List.fold_left (fun env (x, _) -> FullEnvi.add_field [] x env)
      env fields
  | Synonym (name, _, _) | Abstract (name, _) -> FullEnvi.add_typ [] name env

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, Constructors.Gadt constructors) ->
    nest (
      !^ "Inductive" ^^ Name.to_coq name ^^ !^ ":" ^^
      (if typ_args = []
      then empty
      else !^ "forall" ^^ parens @@ nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^-^
      !^ "," ^^ !^ "Type" ^^ !^ ":=" ^-^
      separate empty (constructors |> List.map (fun (constr_name, free_typ_vars, args, res_typ) ->
        newline ^^ nest (
          !^ "|" ^^ Name.to_coq constr_name ^^ !^ ":" ^^
          (match free_typ_vars with
          | [] -> empty
          | free_typ_vars ->
            !^ "forall" ^^ parens (
              separate space (free_typ_vars |> List.map Name.to_coq) ^^ !^ ":" ^^ !^ "Type"
            ) ^-^ !^ ",") ^^
          separate space (args |> List.map (fun arg -> Type.to_coq true arg ^^ !^ "->")) ^^
          Type.to_coq false res_typ
        ))) ^-^ !^ "." ^^
      separate empty (constructors |> List.map (fun (constr_name, free_typ_vars, args, _) ->
        if free_typ_vars = [] then
          empty
        else
          newline ^^ nest (
            !^ "Arguments" ^^ Name.to_coq constr_name ^^
            braces (separate space (List.map Name.to_coq free_typ_vars)) ^^
            separate space (List.map (fun _ -> !^ "_") args)
            ^-^ !^ "."
          )
      ))
    )
  | Inductive (name, typ_args, Constructors.NonGadt constructors) ->
    nest (
      !^ "Inductive" ^^ Name.to_coq name ^^
      (if typ_args = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^^
      !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^-^
      separate empty (constructors |> List.map (fun (constr_name, args) ->
        newline ^^ nest (
          !^ "|" ^^ Name.to_coq constr_name ^^ !^ ":" ^^
          separate space (args |> List.map (fun arg -> Type.to_coq true arg ^^ !^ "->")) ^^
          separate space (List.map Name.to_coq (name :: typ_args))
        ))) ^-^ !^ "." ^^
      separate empty (constructors |> List.map (fun (constr_name, args) ->
        if typ_args = [] then
          empty
        else
          newline ^^ nest (
            !^ "Arguments" ^^ Name.to_coq constr_name ^^
            braces (separate space (List.map Name.to_coq typ_args)) ^-^
            concat (List.map (fun _ -> space ^^ !^ "_") args)
            ^-^ !^ "."
          )
      ))
    )
  | Record (name, fields) ->
    nest (
      !^ "Record" ^^ Name.to_coq name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}.")
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      (match typ_args with
      | [] -> empty
      | _ -> parens (separate space (List.map Name.to_coq typ_args) ^^ !^ ":" ^^ !^ "Type")) ^^
      !^ ":=" ^^ Type.to_coq false value ^-^ !^ "."
    )
  | Abstract (name, typ_args) ->
    nest (
      !^ "Parameter" ^^ Name.to_coq name ^^ !^ ":" ^^
      (match typ_args with
      | [] -> empty
      | _ :: _ ->
        !^ "forall" ^^ braces (group (
          separate space (List.map Name.to_coq typ_args) ^^
          !^ ":" ^^ !^ "Type")) ^-^ !^ ",") ^^
      !^ "Type" ^-^ !^ ".")
