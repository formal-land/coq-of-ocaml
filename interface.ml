open SmartPrint
open Yojson.Basic

module Shape = struct
  type t = PathName.t list list

  let rec pp (shape : t) : SmartPrint.t =
    OCaml.list (OCaml.list PathName.pp) shape

  let rec of_effect_typ (typ : Effect.Type.t) : t =
    match typ with
    | Effect.Type.Pure -> []
    | Effect.Type.Arrow (d, typ) ->
      let ds = Effect.Descriptor.elements d |> List.map (fun x ->
        x.BoundName.path_name) in
      ds :: of_effect_typ typ

  let to_effect_typ (shape : t) (env : 'a FullEnvi.t) : Effect.Type.t =
    let descriptor ds : Effect.Descriptor.t =
      let ds = ds |> List.map (fun d ->
        Effect.Descriptor.singleton (Effect.Descriptor.Id.Ether d)
          (Envi.bound_name Loc.Unknown d env.FullEnvi.descriptors)) in
      Effect.Descriptor.union ds in
    List.fold_right (fun ds typ -> Effect.Type.Arrow (descriptor ds, typ))
      shape Effect.Type.Pure

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

let of_typ_definition (typ_def : Structure.TypeDefinition.t) : t list =
  match typ_def with
  | Structure.TypeDefinition.Inductive (name, _, constructors) ->
    Typ name :: List.map (fun (x, _) -> Constructor x) constructors
  | Structure.TypeDefinition.Record (name, fields) ->
    Typ name :: List.map (fun (x, _) -> Field x) fields
  | Structure.TypeDefinition.Synonym (name, _, _) -> [Typ name]

let rec of_structures (defs : ('a * Effect.t) Structure.t list) : t list =
  List.flatten (List.map of_structure defs)

and of_structure (def : ('a * Effect.t) Structure.t) : t list =
  match def with
  | Structure.Value (_, value) ->
    let values = value.Exp.Definition.cases |> List.map (fun (header, e) ->
      let name = header.Exp.Header.name in
      let typ =
        Effect.function_typ header.Exp.Header.args (snd (Exp.annotation e)) in
      (name, Shape.of_effect_typ @@ Effect.Type.compress typ)) in
    values |> List.map (fun (name, typ) -> Var (name, typ))
  | Structure.TypeDefinition (_, typ_def) -> of_typ_definition typ_def
  | Structure.Exception (_, exn) ->
    let name = exn.Structure.Exception.name in
    [ Descriptor name; Var (name, [[PathName.of_name [] name]]) ]
  | Structure.Reference (_, r) ->
    let name = r.Structure.Reference.name in
    let shape = [[PathName.of_name [] name]] in
    [ Descriptor name;
      Var ("read_" ^ name, shape);
      Var ("write_" ^ name, shape) ]
  | Structure.Open _ -> []
  | Structure.Module (_, name, defs) -> [Interface (name, of_structures defs)]

let rec to_full_envi (interface : t) (env : Effect.Type.t FullEnvi.t)
  : Effect.Type.t FullEnvi.t =
  match interface with
  | Var (x, shape) -> FullEnvi.add_var [] x (Shape.to_effect_typ shape env) env
  | Typ x -> FullEnvi.add_typ [] x env
  | Descriptor x -> FullEnvi.add_descriptor [] x env
  | Constructor x -> FullEnvi.add_constructor [] x env
  | Field x -> FullEnvi.add_field [] x env
  | Interface (x, defs) ->
    let env = FullEnvi.enter_module env in
    let env = List.fold_left (fun env def -> to_full_envi def env) env defs in
    FullEnvi.leave_module x env

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
  let file = open_in_bin file_name in
  let size = in_channel_length file in
  let content = String.make size ' ' in
  really_input file content 0 size;
  of_json_string content