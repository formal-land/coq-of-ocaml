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