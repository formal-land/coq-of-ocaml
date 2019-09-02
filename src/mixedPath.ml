(** A [PathName.t], eventually followed by accesses inside first-class modules. *)
open Typedtree
open Sexplib.Std
open SmartPrint
open Monad.Notations

(** [Access] corresponds to projections from first-class modules. *)
type t =
  | Access of t * PathName.t
  | PathName of PathName.t
  [@@deriving sexp]

(** Shortcut to introduce new local variables for example. *)
let of_name (name : Name.t) : t =
  PathName (PathName.of_name [] name)

let rec of_path_aux (path : Path.t) : (Path.t * (Path.t * string) list) Monad.t =
  match path with
  | Papply _ -> raise "Application of paths is not handled"
  | Pdot (path, field_string, pos) ->
    of_path_aux path >>= fun (path, fields) ->
    begin match fields with
    | [] ->
      (* Get the module declaration of the current [path] to check if it refers
         to a first-class module. *)
      get_env >>= fun env ->
      begin match Env.find_module path env with
      | module_declaration ->
        let { Types.md_type } = module_declaration in
        IsFirstClassModule.is_module_typ_first_class md_type >>= fun is_first_class ->
        begin match is_first_class with
        | None -> return (Path.Pdot (path, field_string, pos), [])
        | Some signature_path -> return (path, [(signature_path, field_string)])
        end
      | exception _ -> raise ("Module '" ^ Path.name path ^ "' not found")
      end
    | _ :: _ -> raise "Nested accesses into first-class modules are not handled (yet)"
    end
  | Pident _ -> return (path, [])

(** The current environemnt must include the potential first-class module signature
    definition of the corresponding projection in the [path]. *)
let of_path (path : Path.t) : t Monad.t =
  of_path_aux path >>= fun (path, fields) ->
  let path_name = PathName.of_path path in
  return (List.fold_left
    (fun mixed_path (signature_path, field_string) ->
      let field_name = Name.of_string field_string in
      let field_path_name = PathName.of_path_and_name signature_path field_name in
      Access (mixed_path, field_path_name))
    (PathName path_name)
    (List.rev fields)
  )

let rec to_coq (path : t) : SmartPrint.t =
  match path with
  | Access (path, field_path_name) ->
    to_coq path ^-^ !^ "." ^-^ parens (PathName.to_coq field_path_name)
  | PathName path_name -> PathName.to_coq path_name
