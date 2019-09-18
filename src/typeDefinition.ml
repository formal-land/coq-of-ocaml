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
      all2
        (match cd_args with
        | Cstr_tuple typs -> typs |> Monad.List.map Type.of_type_expr_without_free_vars
        | Cstr_record _ ->
          set_loc (Loc.of_location cd_loc) (
          raise NotSupported "Unhandled named constructor parameters."))
        (match cd_res with
        | None -> return None
        | Some res ->
          Type.of_type_expr_without_free_vars res >>= fun typ ->
          return (Some typ))
      >>= fun (typs, res_typ) ->
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
  | Inductive of Name.t * Name.t list * Constructors.t
  | Record of Name.t * (Name.t * Type.t) list
  | Synonym of Name.t * Name.t list * Type.t
  | Abstract of Name.t * Name.t list
  [@@deriving sexp]

let of_ocaml (typs : type_declaration list) : t Monad.t =
  match typs with
  | [] -> raise NotSupported "Unexpected type definition with no case"
  | [ { typ_id; typ_type } ] ->
    let name = Name.of_ident typ_id in
    (typ_type.type_params |> Monad.List.map Type.of_type_expr_variable) >>= fun typ_args ->
    (match typ_type.type_kind with
    | Type_variant cases ->
      let mixed_path = MixedPath.of_name name in
      (* The `defined_typ` is useful to give a default return type for non-GADT
         constructors in GADT types. *)
      let defined_typ = Type.Apply (
        mixed_path,
        List.map (fun typ_arg -> Type.Variable typ_arg) typ_args
      ) in
      Constructors.of_ocaml defined_typ cases >>= fun constructors ->
      return (Inductive (name, typ_args, constructors))
    | Type_record (fields, _) ->
      (fields |> Monad.List.map (fun { Types.ld_id = x; ld_type = typ } ->
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return (Name.of_ident x, typ)
      )) >>= fun fields ->
      return (Record (name, fields))
    | Type_abstract ->
      (match typ_type.type_manifest with
      | Some typ ->
        Type.of_type_expr_without_free_vars typ >>= fun typ ->
        return (Synonym (name, typ_args, typ))
      | None -> return (Abstract (name, typ_args)))
    | Type_open -> raise NotSupported "Open type definition not handled.")
  | typ :: _ :: _ -> raise NotSupported "Type definition with 'and' not handled."

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
