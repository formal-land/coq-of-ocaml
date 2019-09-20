open Typedtree
open Sexplib.Std
open SmartPrint
open Monad.Notations

(** The constructors of an inductive type, either in a GADT or non-GADT form. *)
module Constructors = struct
  type t =
    | Gadt of (Name.t * Name.t list * Type.t list * Type.t) list
    | NonGadt of (Name.t * Type.t list) list
    [@@deriving sexp]

  let rec of_ocaml
    (defined_typ : Type.t)
    (cases : Types.constructor_declaration list)
    : t Monad.t =
    match cases with
    | [] -> return (NonGadt [])
    | { cd_args; cd_id; cd_loc; cd_res; } :: cases ->
      set_loc (Loc.of_location cd_loc) (
      let name = Name.of_ident cd_id in
      (match cd_args with
      | Cstr_tuple typs -> typs |> Monad.List.map Type.of_type_expr_without_free_vars
      | Cstr_record labeled_typs ->
        set_loc (Loc.of_location cd_loc) (
        (labeled_typs |> Monad.List.map (fun { Types.ld_type } ->
          Type.of_type_expr_without_free_vars ld_type
        )) >>= fun typs ->
        raise typs NotSupported "Unhandled named constructor parameters.")) >>= fun typs ->
      (match cd_res with
      | None -> return None
      | Some res ->
        Type.of_type_expr_without_free_vars res >>= fun typ ->
        return (Some typ)) >>= fun res_typ ->
      let res_typ_or_defined_typ =
        match res_typ with
        | None -> defined_typ
        | Some res_typ -> res_typ in
      (* We need to compute the free variables to add `forall` annotations in Coq as
         polymorphic variables cannot be infered. *)
      let free_typ_vars = Name.Set.elements (Type.typ_args_of_typs (res_typ_or_defined_typ :: typs)) in
      of_ocaml defined_typ cases >>= fun constructors ->
      (* In case of types mixing GADT and non-GADT constructors, we automatically lift
         to a GADT type. *)
      return (match (res_typ, constructors) with
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
        Gadt ((name, free_typ_vars, typs, res_typ) :: lifted_constructors)))

  let constructor_names (constructors : t) : Name.t list =
    match constructors with
    | Gadt cases -> List.map (fun (x, _, _, _) -> x) cases
    | NonGadt cases -> List.map (fun (x, _) -> x) cases
end

type t =
  | Inductive of (Name.t * Name.t list * Constructors.t) list
  | Record of Name.t * (Name.t * Type.t) list
  | Synonym of Name.t * Name.t list * Type.t
  | Abstract of Name.t * Name.t list
  [@@deriving sexp]

let of_ocaml (typs : type_declaration list) : t Monad.t =
  match typs with
  | [ { typ_id; typ_type = { type_kind = Type_record (fields, _) } } ] ->
    let name = Name.of_ident typ_id in
    (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ } ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (Name.of_ident x, typ)
    )) >>= fun fields ->
    return (Record (name, fields))
  | [ { typ_id; typ_type = { type_kind = Type_abstract; type_manifest; type_params } } ] ->
    let name = Name.of_ident typ_id in
    (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    begin match type_manifest with
    | Some typ ->
      Type.of_type_expr_without_free_vars typ >>= fun typ ->
      return (Synonym (name, typ_args, typ))
    | None -> return (Abstract (name, typ_args))
    end
  | [ { typ_id; typ_type = { type_kind = Type_open } } ] ->
    let name = Name.of_ident typ_id in
    let typ = Type.Apply (MixedPath.of_name "False", []) in
    raise (Synonym (name, [], typ)) NotSupported "Extensible types are not handled"
  | _ ->
    (typs |> Monad.List.filter_map (fun typ ->
      match typ with
      | { typ_id; typ_type = { type_kind = Type_variant cases; type_params } } ->
        let name = Name.of_ident typ_id in
        let mixed_path = MixedPath.of_name name in
        (type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
        (* The `defined_typ` is useful to give a default return type for non-GADT
          constructors in GADT types. *)
        let defined_typ = Type.Apply (
          mixed_path,
          List.map (fun typ_arg -> Type.Variable typ_arg) typ_args
        ) in
        Constructors.of_ocaml defined_typ cases >>= fun constructors ->
        return (Some (name, typ_args, constructors))
      | _ -> raise None NotSupported "Only algebraic data types are supported in mutually recursive types"
    )) >>= fun typs ->
    return (Inductive typs)

let to_coq_inductive
  (is_first : bool)
  (name : Name.t)
  (typ_args : Name.t list)
  (constructors : Constructors.t)
  : SmartPrint.t =
  let keyword = if is_first then !^ "Inductive" else !^ "with" in
  match constructors with
  | Constructors.Gadt constructors ->
    nest (
      keyword ^^ Name.to_coq name ^^ !^ ":" ^^
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
        )))
    )
  | Constructors.NonGadt constructors ->
    nest (
      keyword ^^ Name.to_coq name ^^
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
        )))
    )

let to_coq_inductive_implicits
  (typ_args : Name.t list)
  (constructors : Constructors.t)
  : SmartPrint.t list =
  match constructors with
  | Constructors.Gadt constructors ->
    constructors |> Util.List.filter_map (fun (constr_name, free_typ_vars, args, _) ->
      if free_typ_vars = [] then
        None
      else
        Some (
          nest (
            !^ "Arguments" ^^ Name.to_coq constr_name ^^
            braces (separate space (List.map Name.to_coq free_typ_vars)) ^^
            separate space (List.map (fun _ -> !^ "_") args)
            ^-^ !^ "."
          )
        )
    )
  | Constructors.NonGadt constructors ->
    constructors |> Util.List.filter_map (fun (constr_name, args) ->
      if typ_args = [] then
        None
      else
        Some (
          nest (
            !^ "Arguments" ^^ Name.to_coq constr_name ^^
            braces (separate space (List.map Name.to_coq typ_args)) ^-^
            concat (List.map (fun _ -> space ^^ !^ "_") args)
            ^-^ !^ "."
          )
        )
    )

let to_coq (def : t) : SmartPrint.t =
  match def with
  | Inductive typs ->
    nest (
      separate (newline ^^ newline) (typs |> List.mapi (fun index (name, typ_args, constructors) ->
        let is_first = index = 0 in
        to_coq_inductive is_first name typ_args constructors
      )) ^-^ !^ "." ^^ (
        let constructors_with_implicits =
          typs |>
          List.map (fun (_, typ_args, constructors) ->
            to_coq_inductive_implicits typ_args constructors
          ) |>
          List.concat in
        match constructors_with_implicits with
        | [] -> empty
        | _ :: _ -> newline ^^ separate newline constructors_with_implicits
      )
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
