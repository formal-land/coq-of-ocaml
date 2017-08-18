open Types
open Typedtree
open SmartPrint

type t =
  | Inductive of Name.t * Name.t list * (Name.t * Type.t list) list
  | Record of Name.t * (Name.t * Type.t) list
  | Synonym of Name.t * Name.t list * Type.t
  | Abstract of Name.t * Name.t list

let pp (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    nest (!^ "Inductive" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (OCaml.tuple [
        OCaml.list Name.pp typ_args;
        constructors |> OCaml.list (fun (x, typs) ->
          OCaml.tuple [Name.pp x; OCaml.list Type.pp typs])]))
  | Record (name, fields) ->
    nest (!^ "Record" ^^ Name.pp name ^-^ !^ ":" ^^ newline ^^
      indent (fields |> OCaml.list (fun (x, typ) ->
        OCaml.tuple [Name.pp x; Type.pp typ])))
  | Synonym (name, typ_args, value) ->
    nest (!^ "Synonym" ^^ OCaml.tuple [
      Name.pp name; OCaml.list Name.pp typ_args; Type.pp value])
  | Abstract (name, typ_args) ->
    nest (!^ "Abstract" ^^ OCaml.tuple [
      Name.pp name; OCaml.list Name.pp typ_args])

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (typs : type_declaration list) : t =
  match typs with
  | [] -> Error.raise loc "Unexpected type definition with no case."
  | [{typ_id = name; typ_type = typ}] ->
    let name = Name.of_ident name in
    let typ_args =
      List.map (Type.of_type_expr_variable loc) typ.type_params in
    (match typ.type_kind with
    | Type_variant cases ->
      let constructors =
        let env = FullEnvi.add_typ [] name env in
        cases |> List.map (fun { Types.cd_id = constr; cd_args = args } ->
          let typs =
            match args with
            | Cstr_tuple typs -> typs
            | Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
          (Name.of_ident constr, typs |> List.map (fun typ ->
            Type.of_type_expr env loc typ))) in
      Inductive (name, typ_args, constructors)
    | Type_record (fields, _) ->
      let fields =
        fields |> List.map (fun { Types.ld_id = x; ld_type = typ } ->
          (Name.of_ident x, Type.of_type_expr env loc typ)) in
      Record (name, fields)
    | Type_abstract ->
      (match typ.type_manifest with
      | Some typ -> Synonym (name, typ_args, Type.of_type_expr env loc typ)
      | None -> Abstract (name, typ_args))
      | Type_open -> Error.raise loc "Open type definition not handled.")
  | typ :: _ :: _ -> Error.raise loc "Type definition with 'and' not handled."

let update_env (def : t) (env : 'a FullEnvi.t) : 'a FullEnvi.t =
  match def with
  | Inductive (name, _, constructors) ->
    let env = FullEnvi.add_typ [] name env in
    List.fold_left (fun env (x, _) -> FullEnvi.add_constructor [] x env)
      env constructors
  | Record (name, fields) ->
    let env = FullEnvi.add_typ [] name env in
    List.fold_left (fun env (x, _) -> FullEnvi.add_field [] x env)
      env fields
  | Synonym (name, _, _) | Abstract (name, _) -> FullEnvi.add_typ [] name env

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive (name, typ_args, constructors) ->
    nest (
      !^ "Inductive" ^^ Name.to_coq name ^^
      (if typ_args = []
      then empty
      else parens @@ nest (
        separate space (List.map Name.to_coq typ_args) ^^
        !^ ":" ^^ !^ "Type")) ^^
      !^ ":" ^^ !^ "Type" ^^ !^ ":=" ^-^
      separate empty (constructors |> List.map (fun (constr, args) ->
        newline ^^ nest (
          !^ "|" ^^ Name.to_coq constr ^^ !^ ":" ^^
          separate space (args |> List.map (fun arg -> Type.to_coq true arg ^^ !^ "->")) ^^ separate space (List.map Name.to_coq (name :: typ_args))))) ^-^ !^ "." ^^
      separate empty (constructors |> List.map (fun (name, args) ->
        if typ_args = [] then
          empty
        else
          newline ^^ nest (separate space (
            !^ "Arguments" :: Name.to_coq name ::
            (List.map (fun x -> braces @@ Name.to_coq x) typ_args) @
            (List.map (fun _ -> !^ "_") args)) ^-^ !^ "."))))
  | Record (name, fields) ->
    nest (
      !^ "Record" ^^ Name.to_coq name ^^ !^ ":=" ^^ !^ "{" ^^ newline ^^
      indent (separate (!^ ";" ^^ newline) (fields |> List.map (fun (x, typ) ->
        nest (Name.to_coq x ^^ !^ ":" ^^ Type.to_coq false typ)))) ^^
      !^ "}.")
  | Synonym (name, typ_args, value) ->
    nest (
      !^ "Definition" ^^ Name.to_coq name ^^
      separate space (List.map Name.to_coq typ_args) ^^ !^ ":=" ^^
      Type.to_coq false value ^-^ !^ ".")
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
