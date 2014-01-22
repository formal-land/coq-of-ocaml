(** Types for the effects. *)
open SmartPrint

module Descriptor = struct
  type t = Name.Set.t

  let pp (d : t) : SmartPrint.t =
    OCaml.list Name.pp (Name.Set.elements d)

  let pure : t = Name.Set.empty

  let is_pure (d : t) : bool =
    Name.Set.is_empty d

  let eq (d1 : t) (d2 : t) : bool =
    Name.Set.equal d1 d2

  let of_name (x : Name.t) : t =
    Name.Set.singleton x

  let union (ds : t list) : t =
    List.fold_left (Name.Set.union) pure ds
end

module Type = struct
  type t =
    | Pure
    | Arrow of Descriptor.t * t

  let rec pp (paren : bool) (typ : t) : SmartPrint.t =
    match typ with
    | Pure -> !^ "."
    | Arrow (d, typ) -> Pp.parens paren @@ nest (
      !^ "." ^^
      (if Descriptor.is_pure d then
        !^ "->"
      else
        !^ "-" ^-^ Descriptor.pp d ^-^ !^ "->") ^^
      pp false typ)

  let rec is_pure (typ : t) : bool =
    match typ with
    | Pure -> true
    | Arrow (d, typ) -> Descriptor.is_pure d && is_pure typ

  let rec eq (typ1 : t) (typ2 : t) : bool =
    match (typ1, typ2) with
    | (Pure, _) -> is_pure typ2
    | (_, Pure) -> is_pure typ1
    | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
      (Descriptor.eq d1 d2) && eq typ1 typ2

  let return_descriptor (typ : t) : Descriptor.t =
    match typ with
    | Pure -> Descriptor.pure
    | Arrow (d, _) -> d

  let return_type (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (_, typ) -> typ

  let union (typs : t list) : t =
    let rec aux typ1 typ2 =
      match (typ1, typ2) with
      | (Pure, _) -> if is_pure typ2 then Pure else typ2
      | (_, Pure) -> if is_pure typ1 then Pure else typ1
      | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
        Arrow (Descriptor.union [d1; d2], aux typ1 typ2) in
    List.fold_left aux Pure typs
end

module Env = struct
  (** A non-empty list of maps. *)
  type t = Type.t PathName.Map.t list

  let pp (effects : t) : SmartPrint.t =
    List.map PathName.Map.bindings effects |>
    List.concat |>
    OCaml.list (fun (x, typ) ->
      nest (PathName.pp x ^^ !^ ":" ^^ Type.pp false typ))

  let empty : t = [PathName.Map.empty]

  let add (x : PathName.t) (typ : Type.t) (effects : t) : t =
    match effects with
    | map :: effects -> PathName.Map.add x typ map :: effects
    | [] -> failwith "Effects must be a non-empty list."

  let rec find (x : PathName.t) (effects : t) : Type.t =
    match effects with
    | map :: effects ->
      (try PathName.Map.find x map with
      | Not_found -> find x effects)
    | [] -> raise Not_found

  let open_module (effects : t) : t =
    PathName.Map.empty :: effects

  let close_module (effects : t) (name : string) : t =
    match effects with
    | map1 :: map2 :: effects ->
      PathName.Map.fold (fun x typ map ->
        let { PathName.path = path; base = base } = x in
        PathName.Map.add { PathName.path = name :: path; base = base } typ map)
        map1 map2
        :: effects
    | _ -> failwith "At least one module should be opened."

  let in_function (effects : t) (args_names : Name.t list) : t =
    List.fold_left (fun effects x ->
      add (PathName.of_name [] x) Type.Pure effects)
      effects args_names
end

type t = { descriptor : Descriptor.t; typ : Type.t }

let pp (effect : t) : SmartPrint.t =
  nest (!^ "Effect" ^^ Pp.list [
    Descriptor.pp effect.descriptor; Type.pp false effect.typ])

let function_typ (args_names : Name.t list) (body_effect : t)
  : Type.t option =
  match args_names with
  | [] ->
    if Descriptor.is_pure body_effect.descriptor then
      Some body_effect.typ
    else
      None
  | _ :: args_names ->
    Some (List.fold_left (fun effect_typ _ ->
      Type.Arrow (Descriptor.pure, effect_typ))
      (Type.Arrow
          (body_effect.descriptor, body_effect.typ))
      args_names)

let union (effects : t list) : t =
  { descriptor =
      Descriptor.union @@ List.map (fun effect -> effect.descriptor) effects;
    typ = Type.union (List.map (fun effect -> effect.typ) effects) }