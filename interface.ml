open SmartPrint
open Yojson.Safe

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

  let to_json (shape : t) : json =
    `List (List.map (fun ds -> `List (List.map PathName.to_json ds)) shape)

  let of_json (json : json) : t =
    let of_list f json =
      match json with
      | `List jsons -> List.map f jsons
      | _ -> failwith "List expected." in
    of_list (of_list PathName.of_json) json
end

module Declaration = struct
  type t =
    | Var of Name.t * Shape.t
    | Typ of Name.t
    | Descriptor of Name.t
    | Constructor of Name.t
    | Field of Name.t

  let pp (d : t) : SmartPrint.t =
    match d with
    | Var (x, shape) ->
      !^ "Var" ^^ OCaml.tuple [Name.pp x; Shape.pp shape]
    | Typ x -> !^ "Typ" ^^ Name.pp x
    | Descriptor x -> !^ "Descriptor" ^^ Name.pp x
    | Constructor x -> !^ "Constructor" ^^ Name.pp x
    | Field x -> !^ "Field" ^^ Name.pp x

  let to_json (d : t) : json =
    match d with
    | Var (x, shape) ->
      `Variant ("Var", Some (`List [Name.to_json x; Shape.to_json shape]))
    | Typ x -> `Variant ("Typ", Some (Name.to_json x))
    | Descriptor x -> `Variant ("Descriptor", Some (Name.to_json x))
    | Constructor x -> `Variant ("Constructor", Some (Name.to_json x))
    | Field x -> `Variant ("Field", Some (Name.to_json x))

  let of_json (json : json) : t =
    match json with
    | `List [`String c; arg] ->
      (match (c, arg) with
      | ("Var", `List [x; shape]) -> Var (Name.of_json x, Shape.of_json shape)
      | ("Typ", x) -> Typ (Name.of_json x)
      | ("Descriptor", x) -> Descriptor (Name.of_json x)
      | ("Constructor", x) -> Constructor (Name.of_json x)
      | ("Field", x) -> Field (Name.of_json x)
      | _ -> failwith "Unknown field.")
    | _ -> failwith "List expected."
end

type t =
  | Declaration of Declaration.t
  | Interface of Name.t * t list

let rec pp (interface : t) : SmartPrint.t =
  match interface with
  | Declaration d -> Declaration.pp d
  | Interface (x, ds) ->
    !^ "Interface" ^^ Name.pp x ^^ !^ "=" ^^ newline ^^ indent
      (separate newline (List.map pp ds))

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
    values |> List.map (fun (name, typ) ->
      Declaration (Declaration.Var (name, typ)))
  | Structure.Inductive (_, ind) ->
    let name = ind.Structure.Inductive.name in
    let constructors = List.map fst ind.Structure.Inductive.constructors in
    Declaration (Declaration.Typ name) :: List.map (fun x ->
      Declaration (Declaration.Constructor x)) constructors
  | Structure.Record (_, r) ->
    let name = r.Structure.Record.name in
    let fields = List.map fst r.Structure.Record.fields in
    Declaration (Declaration.Typ name) :: List.map (fun x ->
      Declaration (Declaration.Field x)) fields
  | Structure.Synonym (_, s) ->
    [Declaration (Declaration.Typ s.Structure.Synonym.name)]
  | Structure.Exception (_, exn) ->
    let name = exn.Structure.Exception.name in
    [ Declaration (Declaration.Descriptor name);
      Declaration (Declaration.Var (name, [[PathName.of_name [] name]])) ]
  | Structure.Reference (_, r) ->
    let name = r.Structure.Reference.name in
    let shape = [[PathName.of_name [] name]] in
    [ Declaration (Declaration.Descriptor name);
      Declaration (Declaration.Var ("read_" ^ name, shape));
      Declaration (Declaration.Var ("write_" ^ name, shape)) ]
  | Structure.Open _ -> []
  | Structure.Module (_, name, defs) -> [Interface (name, of_structures defs)]

let rec to_json (interface : t) : json =
  match interface with
  | Declaration d -> `Variant ("Declaration", Some (Declaration.to_json d))
  | Interface (x, ds) ->
    `Variant ("Interface",
      Some (`List [Name.to_json x; `List (List.map to_json ds)]))

let rec of_json (json : json) : t =
  match json with
  | `List [`String "Declaration"; d] -> Declaration (Declaration.of_json d)
  | `List [`String "Interface"; `List [x; `List ds]] ->
    Interface (Name.of_json x, List.map of_json ds)
  | _ -> failwith "Wrong JSON format."

let to_json_string (interface : t) : string =
  pretty_to_string ~std:true (`Assoc [
    "content", to_json interface;
    "version", `String "1"])

let of_json_string (json : string) : t =
  match from_string json with
  | `Assoc jsons ->
    (match List.assq "version" jsons with
    | `String "1" -> of_json @@ List.assq "content" jsons
    | _ -> failwith "Wrong interface version.")
  | _ -> failwith "Wrong JSON format."