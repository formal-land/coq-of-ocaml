open SmartPrint
open Yojson.Basic

module Shape = struct
  type t = PathName.t list list

  let rec pp (shape : t) : SmartPrint.t =
    OCaml.list (OCaml.list PathName.pp) shape

  let to_json (shape : t) : json =
    `List (List.map (fun ds -> `List (List.map PathName.to_json ds)) shape)

  let of_json (json : json) : t =
    let of_list f json =
      match json with
      | `List jsons -> List.map f jsons
      | _ -> raise (Error.Json "List expected.") in
    of_list (of_list PathName.of_json) json
end

type t =
  | Var of Name.t * Shape.t
  | Typ of Name.t
  | Descriptor of Name.t
  | Constructor of Name.t
  | Field of Name.t
  | Interface of Name.t * t list

let rec pp (interface : t) : SmartPrint.t =
  match interface with
  | Var (x, shape) -> !^ "Var" ^^ OCaml.tuple [Name.pp x; Shape.pp shape]
  | Typ x -> !^ "Typ" ^^ Name.pp x
  | Descriptor x -> !^ "Descriptor" ^^ Name.pp x
  | Constructor x -> !^ "Constructor" ^^ Name.pp x
  | Field x -> !^ "Field" ^^ Name.pp x
  | Interface (x, defs) ->
    !^ "Interface" ^^ Name.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp defs))

let of_typ_definition (typ_def : TypeDefinition.t) : t list =
  match typ_def with
  | TypeDefinition.Inductive (name, _, constructors) ->
    Typ name :: List.map (fun (x, _) -> Constructor x) constructors
  | TypeDefinition.Record (name, fields) ->
    Typ name :: List.map (fun (x, _) -> Field x) fields
  | TypeDefinition.Synonym (name, _, _) | TypeDefinition.Abstract (name, _) ->
    [Typ name]

let rec to_json (interface : t) : json =
  match interface with
  | Var (x, shape) ->
    `List [`String "Var"; Name.to_json x; Shape.to_json shape]
  | Typ x -> `List [`String "Typ"; Name.to_json x]
  | Descriptor x -> `List [`String "Descriptor"; Name.to_json x]
  | Constructor x -> `List [`String "Constructor"; Name.to_json x]
  | Field x -> `List [`String "Field"; Name.to_json x]
  | Interface (x, defs) ->
    `List [`String "Interface"; Name.to_json x; `List (List.map to_json defs)]

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Var"; x; shape] ->
    Var (Name.of_json x, Shape.of_json shape)
  | `List [`String "Typ"; x] -> Typ (Name.of_json x)
  | `List [`String "Descriptor"; x] -> Descriptor (Name.of_json x)
  | `List [`String "Constructor"; x] -> Constructor (Name.of_json x)
  | `List [`String "Field"; x] -> Field (Name.of_json x)
  | `List [`String "Interface"; x; `List defs] ->
      Interface (Name.of_json x, List.map of_json defs)
  | _ -> raise (Error.Json
    "Expected a Var, Typ, Descriptor, Constructor, Field or Interface field.")

let to_json_string (interface : t) : string =
  let pretty = pretty_format ~std:true (`Assoc [
    "version", `String "1";
    "content", to_json interface]) in
  let buffer = Buffer.create 0 in
  let formatter = Format.formatter_of_buffer buffer in
  Format.pp_set_margin formatter 120;
  Easy_format.Pretty.to_formatter formatter pretty;
  Format.pp_print_flush formatter ();
  Buffer.contents buffer

let of_json_string (json : string) : t =
  match from_string json with
  | `Assoc jsons ->
    (match List.assoc "version" jsons with
    | `String "1" -> of_json @@ List.assoc "content" jsons
    | _ -> raise (Error.Json "Wrong interface version, expected 1."))
  | _ -> raise (Error.Json "Expected an object.")

let of_file (file_name : string) : t =
  let file =
    try open_in_bin file_name with
    | Sys_error _ ->
      open_in_bin (Filename.dirname Sys.executable_name ^
        "/../share/coq-of-ocaml/" ^ file_name) in
  let size = in_channel_length file in
  let content = String.make size ' ' in
  really_input file content 0 size;
  of_json_string content
