(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open Typedtree
open Sexplib.Std
open SmartPrint

(** [Access] corresponds to projections from first-class modules. *)
type t =
  | Access of t * PathName.t
  | PathName of PathName.t
  [@@deriving sexp]

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

let rec of_path_aux (env : Env.t) (loc : Loc.t) (path : Path.t) : Path.t * (Path.t * string) list =
  match path with
  | Papply _ -> Error.raise loc "Application of paths is not handled"
  | Pdot (path, field_string, pos) ->
    let (path, fields) = of_path_aux env loc path in
    begin match fields with
    | [] ->
      (* Get the module declaration of the current [path] to check if it refers
         to a first-class module. *)
      begin match Env.find_module path env with
      | module_declaration ->
        let { Types.md_type } = module_declaration in
        begin match IsFirstClassModule.is_module_typ_first_class env loc md_type with
        | None -> (Pdot (path, field_string, pos), [])
        | Some signature_path -> (path, [(signature_path, field_string)])
        end
      | exception _ -> Error.raise loc "Unexpected module not found"
      end
    | _ :: _ -> Error.raise loc "Nested accesses into first-class modules are not handled (yet)"
    end
  | Pident _ -> (path, [])

(** The [env] must include the potential first-class module signature definition of
    the corresponding projection in the [path]. *)
let of_path (env : Env.t) (loc : Loc.t) (path : Path.t) : t =
  let (path, fields) = of_path_aux env loc path in
  let path_name = PathName.of_path loc path in
  List.fold_left
    (fun mixed_path (signature_path, field_string) ->
      let field_name = Name.of_string field_string in
      let field_path_name = PathName.of_path_and_name loc signature_path field_name in
      Access (mixed_path, field_path_name))
    (PathName path_name)
    (List.rev fields)

let rec to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, field_path_name) ->
    parens (!^ "projT2" ^^ to_coq path) ^-^ !^ "." ^-^ parens (PathName.to_coq field_path_name)
  | PathName path_name -> PathName.to_coq path_name
