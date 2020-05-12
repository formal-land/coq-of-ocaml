(** Global identifiers with a module path, used to reference a definition for example. *)
open SmartPrint
open Monad.Notations

type t = {
  path : Name.t list;
  base : Name.t }

(** Internal helper for this module. *)
let __make (path : string list) (base : string) : t =
  {
    path = path |> List.map (fun name -> Name.Make name);
    base = Name.Make base
  }

let try_to_use (head : string) (name : string) : bool option Monad.t =
  let* configuration = get_configuration in
  let require = Configuration.should_require configuration head in
  let require_import = Configuration.should_require_import configuration head in
  match (require, require_import) with
  | (_, Some require_import) ->
    let* () = use true require_import name in
    return (Some true)
  | (Some require, _) ->
    let* () = use false require name in
    return (Some false)
  | (None, None) -> return None


(* Convert an identifier from OCaml to its Coq's equivalent, or [None] if no
   conversion is needed. We consider all the paths in the standard library
   to be converted, as conversion also means keeping the name as it (without
   taking into accounts that the stdlib was open). *)
let try_convert (path_name : t) : t option Monad.t =
  let make path base = return (Some (__make path base)) in
  let { path; base } = path_name in
  let path = path |> List.map Name.to_string in
  let base = Name.to_string base in
  (* The core library *)
  match path with
  | [] ->
    begin match base with
    (* Built-in types *)
    | "int" -> make [] "int"
    | "float" -> make [] "float"
    | "char" -> make [] "ascii"
    | "bytes" -> make [] "bytes"
    | "string" -> make [] "string"
    | "bool" -> make [] "bool"
    | "false" -> make [] "false"
    | "true" -> make [] "true"
    | "unit" -> make [] "unit"
    | "()" -> make [] "tt"
    | "list" -> make [] "list"
    | "[]" -> make [] "[]"
    | "op_coloncolon" -> make [] "cons"
    | "option" -> make [] "option"
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | "Ok" -> make [] "inl"
    | "Error" -> make [] "inr"
    | "exn" -> make [] "extensible_type"

    (* Predefined exceptions *)
    | "Match_failure" -> make ["OCaml"] "Match_failure"
    | "Assert_failure" -> make ["OCaml"] "Assert_failure"
    | "Invalid_argument" -> make ["OCaml"] "Invalid_argument"
    | "Failure" -> make ["OCaml"] "Failure"
    | "Not_found" -> make ["OCaml"] "Not_found"
    | "Out_of_memory" -> make ["OCaml"] "Out_of_memory"
    | "Stack_overflow" -> make ["OCaml"] "Stack_overflow"
    | "Sys_error" -> make ["OCaml"] "Sys_error"
    | "End_of_file" -> make ["OCaml"] "End_of_file"
    | "Division_by_zero" -> make ["OCaml"] "Division_by_zero"
    | "Sys_blocked_io" -> make ["OCaml"] "Sys_blocked_io"
    | "Undefined_recursive_module" -> make ["OCaml"] "Undefined_recursive_module"
    | _ -> return None
    end

  (* Optional parameters *)
  | ["*predef*"] ->
    begin match base with
    | "None" -> make [] "None"
    | "Some" -> make [] "Some"
    | _ -> return None
    end

  (* Stdlib *)
  | ["Stdlib"] ->
    begin match base with
    (* Exceptions *)
    | "invalid_arg" -> make ["OCaml"; "Stdlib"] "invalid_arg"
    | "failwith" -> make ["OCaml"; "Stdlib"] "failwith"
    | "Exit" -> make ["OCaml"; "Stdlib"] "Exit"
    (* Comparisons *)
    | "op_eq" -> make [] "equiv_decb"
    | "op_ltgt" -> make [] "nequiv_decb"
    | "op_lt" -> make ["OCaml"; "Stdlib"] "lt"
    | "op_gt" -> make ["OCaml"; "Stdlib"] "gt"
    | "op_lteq" -> make ["OCaml"; "Stdlib"] "le"
    | "op_gteq" -> make ["OCaml"; "Stdlib"] "ge"
    | "compare" -> make ["OCaml"; "Stdlib"] "compare"
    | "min" -> make ["OCaml"; "Stdlib"] "min"
    | "max" -> make ["OCaml"; "Stdlib"] "max"
    (* Boolean operations *)
    | "not" -> make [] "negb"
    | "op_andand" -> make [] "andb"
    | "op_and" -> make [] "andb"
    | "op_pipepipe" -> make [] "orb"
    | "or" -> make [] "orb"
    (* Integer arithmetic *)
    | "op_tildeminus" -> make ["Z"] "opp"
    | "op_tildeplus" -> make []  ""
    | "succ" -> make ["Z"] "succ"
    | "pred" -> make ["Z"] "pred"
    | "op_plus" -> make ["Z"] "add"
    | "op_minus" -> make ["Z"] "sub"
    | "op_star" -> make ["Z"] "mul"
    | "op_div" -> make ["Z"] "div"
    | "__mod" -> make ["Z"] "modulo"
    | "abs" -> make ["Z"] "abs"
    (* Bitwise operations *)
    | "land" -> make ["Z"] "land"
    | "lor" -> make ["Z"] "lor"
    | "lxor" -> make ["Z"] "lxor"
    | "lsl" -> make ["Z"] "shiftl"
    | "lsr" -> make ["Z"] "shiftr"
    (* Floating-point arithmetic *)
    (* String operations *)
    | "op_caret" -> make ["String"] "append"
    (* Character operations *)
    | "int_of_char" -> make ["OCaml"; "Stdlib"] "int_of_char"
    | "char_of_int" -> make ["OCaml"; "Stdlib"] "char_of_int"
    (* Unit operations *)
    | "ignore" -> make ["OCaml"; "Stdlib"] "ignore"
    (* String conversion functions *)
    | "string_of_bool" -> make ["OCaml"; "Stdlib"] "string_of_bool"
    | "bool_of_string" -> make ["OCaml"; "Stdlib"] "bool_of_string"
    | "string_of_int" -> make ["OCaml"; "Stdlib"] "string_of_int"
    | "int_of_string" -> make ["OCaml"; "Stdlib"] "int_of_string"
    (* Pair operations *)
    | "fst" -> make [] "fst"
    | "snd" -> make [] "snd"
    (* List operations *)
    | "op_at" -> make ["OCaml"; "Stdlib"] "app"
    (* Input/output *)
    (* Output functions on standard output *)
    | "print_char" -> make ["OCaml"; "Stdlib"] "print_char"
    | "print_string" -> make ["OCaml"; "Stdlib"] "print_string"
    | "print_int" -> make ["OCaml"; "Stdlib"] "print_int"
    | "print_endline" -> make ["OCaml"; "Stdlib"] "print_endline"
    | "print_newline" -> make ["OCaml"; "Stdlib"] "print_newline"
    (* Output functions on standard error *)
    | "prerr_char" -> make ["OCaml"; "Stdlib"] "prerr_char"
    | "prerr_string" -> make ["OCaml"; "Stdlib"] "prerr_string"
    | "prerr_int" -> make ["OCaml"; "Stdlib"] "prerr_int"
    | "prerr_endline" -> make ["OCaml"; "Stdlib"] "prerr_endline"
    | "prerr_newline" -> make ["OCaml"; "Stdlib"] "prerr_newline"
    (* Input functions on standard input *)
    | "read_line" -> make ["OCaml"; "Stdlib"] "read_line"
    | "read_int" -> make ["OCaml"; "Stdlib"] "read_int"
    (* General output functions *)
    (* General input functions *)
    (* Operations on large files *)
    (* References *)
    (* Result type *)
    | "result" -> make [] "sum"
    (* Operations on format strings *)
    (* Program termination *)
    | _ -> return (Some path_name)
    end

  (* Bytes *)
  | ["Stdlib"; "Bytes"] ->
    begin match base with
    | "cat" -> make ["String"] "append"
    | "concat" -> make ["String"] "concat"
    | "length" -> make ["String"] "length"
    | "sub" -> make ["String"] "sub"
    | _ -> return (Some path_name)
    end

  (* List *)
  | ["Stdlib"; "List"] ->
    begin match base with
    | "exists" -> make ["OCaml"; "List"] "_exists"
    | "exists2" -> make ["OCaml"; "List"] "_exists2"
    | "length" -> make ["OCaml"; "List"] "length"
    | "map" -> make ["List"] "map"
    | "rev" -> make ["List"] "rev"
    | _ -> return (Some path_name)
    end

  (* Seq *)
  | ["Stdlib"; "Seq"] ->
    begin match base with
    | "t" -> make ["OCaml"; "Seq"] "t"
    | _ -> return (Some path_name)
    end

  (* String *)
  | ["Stdlib"; "String"] ->
    begin match base with
    | "length" -> make ["OCaml"; "String"] "length"
    | _ -> return (Some path_name)
    end

  | _ ->
    begin match (path, base) with
    | (source :: name :: rest, _) ->
      let* is_import = try_to_use source name in
      begin match is_import with
      | None -> return None
      | Some import ->
        if import then
          make rest base
        else
          make (name :: rest) base
      end
    | ([source], name) ->
      let* is_import = try_to_use source name in
      begin match is_import with
      | None -> return None
      | Some _ -> make [] base
      end
    | _ -> return None
    end

let convert (path_name : t) : t Monad.t =
  try_convert path_name >>= fun conversion ->
  match conversion with
  | None -> return path_name
  | Some path_name -> return path_name

(** Lift a local name to a global name. *)
let of_name (path : Name.t list) (base : Name.t) : t =
  { path; base }

(** Import an OCaml [Longident.t]. *)
let of_long_ident (is_value : bool) (long_ident : Longident.t) : t Monad.t =
  let* configuration = get_configuration in
  let* () =
    match Longident.flatten long_ident with
    | head :: _ ->
      let require =
        Configuration.should_require_long_ident configuration head in
      begin match require with
      | None -> return ()
      | Some require -> use false require head
      end
    | [] -> return () in
  match List.rev (Longident.flatten long_ident) with
  | [] -> failwith "Unexpected Longident.t with an empty list"
  | x :: xs ->
    (xs |> List.rev |> Monad.List.map (Name.of_string is_value)) >>= fun path ->
    let* name = Name.of_string is_value x in
    return (of_name path name)

(** Split an [Ident.t] in case of flattened module names. *)
let split_ident (is_value : bool) (ident : Ident.t)
  : (Name.t list * Name.t) Monad.t =
  let ident_elements =
    Str.split (Str.regexp_string "__") (Ident.name ident) |>
    List.rev in
  match ident_elements with
  | base :: path ->
    let base =
      match path with
      | [] -> base
      | _ :: _ -> String.capitalize_ascii base in
    let* path = Monad.List.map (Name.of_string false) path in
    let* base = Name.of_string is_value base in
    return (List.rev path, base)
  | [] -> assert false

(** Import an OCaml [Path.t]. *)
let of_path_without_convert (is_value : bool) (path : Path.t) : t Monad.t =
  let rec aux path : (Name.t list * Name.t) Monad.t =
    match path with
    | Path.Pident ident -> split_ident is_value ident
    | Path.Pdot (path, field) ->
      aux path >>= fun (path, base) ->
      Name.of_string is_value field >>= fun field ->
      return (base :: path, field)
    | Path.Papply _ -> failwith "Unexpected path application" in
  aux path >>= fun (path, base) ->
  return (of_name (List.rev path) base)

let of_path_with_convert (is_value : bool) (path : Path.t) : t Monad.t =
  of_path_without_convert is_value path >>= fun path ->
  convert path

let of_path_and_name_with_convert (path : Path.t) (name : Name.t) : t Monad.t =
  let rec aux p : (Name.t list * Name.t) Monad.t =
    match p with
    | Path.Pident x ->
      let* (path, base) = split_ident false x in
      return (path @ [base], name)
    | Path.Pdot (p, s) ->
      aux p >>= fun (path, base) ->
      Name.of_string false s >>= fun s ->
      return (path @ [s], base)
    | Path.Papply _ -> failwith "Unexpected path application" in
  aux path >>= fun (path, base) ->
  convert (of_name path base)

let map_constructor_name (cstr_name : string) (typ_ident : string)
  : string Monad.t =
  let* configuration = get_configuration in
  let renaming =
    Configuration.is_constructor_renamed configuration typ_ident cstr_name in
  match renaming with
  | Some renaming -> return renaming
  | None -> return cstr_name

let of_constructor_description
  (constructor_description : Types.constructor_description)
  : t Monad.t =
  match constructor_description with
  | {
      cstr_name;
      cstr_res = { desc = Tconstr (path, _, _); _ };
      _
    } ->
    let typ_ident = Path.head path in
    of_path_without_convert false path >>= fun { path; _ } ->
    let* cstr_name = map_constructor_name cstr_name (Ident.name typ_ident) in
    Name.of_string false cstr_name >>= fun base ->
    convert { path; base }
  | { cstr_name; _ } ->
    Name.of_string false cstr_name >>= fun cstr_name ->
    let path = of_name [] cstr_name in
    raise
      path
      Unexpected
      "Unexpected constructor description without a type constructor"

let rec iterate_in_aliases (path : Path.t) : Path.t Monad.t =
  let* configuration = get_configuration in
  let is_in_barrier_module (path : Path.t) : bool =
    Configuration.is_alias_in_barrier_module
      configuration
      (Ident.name (Path.head path)) in
  get_env >>= fun env ->
  match Env.find_type path env with
  | { type_manifest = Some { desc = Tconstr (path', _, _); _ }; _ } ->
    if is_in_barrier_module path && not (is_in_barrier_module path') then
      return path
    else
      iterate_in_aliases path'
  | _ -> return path

let of_label_description (label_description : Types.label_description)
  : t Monad.t =
  match label_description with
  | { lbl_name; lbl_res = { desc = Tconstr (path, _, _); _ } ; _ } ->
    iterate_in_aliases path >>= fun path ->
    of_path_without_convert false path >>= fun { path; base } ->
    Name.of_string false lbl_name >>= fun lbl_name ->
    let path_name = {
      path = path @ [base];
      base = lbl_name } in
    convert path_name
  | { lbl_name; _ } ->
    Name.of_string false lbl_name >>= fun lbl_name ->
    let path = of_name [] lbl_name in
    raise
      path
      Unexpected
      "Unexpected label description without a type constructor"

let constructor_of_variant (label : string) : t Monad.t =
  let* configuration = get_configuration in
  let constructor =
    Configuration.get_variant_constructor configuration label in
  match constructor with
  | Some constructor ->
    return { path = []; base = Name.of_string_raw constructor }
  | None ->
    Name.of_string false label >>= fun base ->
    raise
      { path = []; base }
      NotSupported
      ("Constructor of the variant `" ^ label ^ " unknown")

let get_head_and_tail (path_name : t) : Name.t * t option =
  let { path; base } = path_name in
  match path with
  | [] -> (base, None)
  | head :: path -> (head, Some { path; base })

let add_prefix (prefix : Name.t) (path_name : t) : t =
  let { path; base } = path_name in
  { path = prefix :: path; base }

let is_tt (path_name : t) : bool =
  match (path_name.path, Name.to_string path_name.base) with
  | ([], "tt") -> true
  | _ -> false

let is_unit (path : Path.t) : bool =
  Path.name path = "unit"

let false_value : t =
  { path = []; base = Name.Make "false" }

let true_value : t =
  { path = []; base = Name.Make "true" }

let prefix_by_with (path_name : t) : t =
  let { path; base } = path_name in
  { path; base = Name.prefix_by_with base }

let compare_paths (path1 : Path.t) (path2 : Path.t) : int Monad.t =
  let import_path (path : Path.t) : t Monad.t =
    of_path_without_convert false path in
  import_path path1 >>= fun path1 ->
  import_path path2 >>= fun path2 ->
  return (compare path1 path2)

let to_string (x : t) : string =
  String.concat "." (List.map Name.to_string (x.path @ [x.base]))

let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))

let typ_of_variant (label : string) : t option Monad.t =
  let* configuration = get_configuration in
  let typ = Configuration.get_variant_typ configuration label in
  match typ with
  | Some typ -> return (Some { path = []; base = Name.of_string_raw typ })
  | None -> return None

let typ_of_variants (labels : string list) : t option Monad.t =
  let* typs = labels |> Monad.List.filter_map typ_of_variant in
  let typs = typs |> List.sort_uniq compare in
  let variants_message =
    String.concat ", " (labels |> List.map (fun label -> "`" ^ label)) in
  match typs with
  | [] ->
    raise
      None
      NotSupported
      ("No type known for the following variants: " ^ variants_message)
  | [typ] -> return (Some typ)
  | typ :: _ :: _ ->
    raise
      (Some typ)
      NotSupported
      (
        "At least two types found for the variants " ^ variants_message ^
        ":\n" ^
        String.concat "\n" (typs |> List.map (fun typ ->
          "- " ^ Pp.to_string (to_coq typ)
        ))
      )
