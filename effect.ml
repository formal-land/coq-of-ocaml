(** Types for the effects. *)
open SmartPrint

module Type' = Type

module Type = struct
  type t =
    | Pure
    | Arrow of bool * t

  let rec pp (paren : bool) (typ : t) : SmartPrint.t =
    match typ with
    | Pure -> !^ "."
    | Arrow (effect, typ) -> Pp.parens paren @@ nest (
      !^ "." ^^ (if effect then !^ "-e->" else !^ "->") ^^
      pp false typ)

  let rec is_pure (typ : t) : bool =
    match typ with
    | Pure -> true
    | Arrow (effect, typ) -> not effect && is_pure typ

  let rec eq (typ1 : t) (typ2 : t) : bool =
    match (typ1, typ2) with
    | (Pure, _) -> is_pure typ2
    | (_, Pure) -> is_pure typ1
    | (Arrow (effect1, typ1), Arrow (effect2, typ2)) ->
      (effect1 = effect2) && eq typ1 typ2

  let return_effect (typ : t) : bool =
    match typ with
    | Pure -> false
    | Arrow (effect, _) -> effect

  let return_type (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (_, typ) -> typ

  let unify (typs : t list) : t =
    let rec aux typ1 typ2 =
      match (typ1, typ2) with
      | (Pure, _) -> if is_pure typ2 then Pure else typ2
      | (_, Pure) -> if is_pure typ1 then Pure else typ1
      | (Arrow (effect1, typ1), Arrow (effect2, typ2)) ->
        Arrow (effect1 && effect2, aux typ1 typ2) in
    List.fold_left aux Pure typs

  let rec monadise (typ : Type.t) (effect_typ : t) : Type.t =
    match (typ, effect_typ) with
    | (Type.Variable _, Pure) | (Type.Tuple _, Pure)
      | (Type.Apply _, Pure) | (Type.Arrow _, Pure) -> typ
    | (Type.Arrow (typ1, typ2), Arrow (effect, effect_typ2)) ->
      let typ2 = monadise typ2 effect_typ2 in
      Type.Arrow (typ1, if effect then Type.Monad typ2 else typ2)
    | (Type.Monad _, _) -> failwith "This type is already monadic."
    | _ -> failwith "Type and effect type are not compatible."
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

  let in_function (effects : t) (args : (Name.t * Type'.t) list) : t =
    List.fold_left (fun effects (x, _) ->
      add (PathName.of_name [] x) Type.Pure effects)
      effects args
end

type t = { effect : bool; typ : Type.t }

let pp (effect : t) : SmartPrint.t =
  nest (!^ "Effect" ^^ Pp.list [
    OCaml.bool effect.effect; Type.pp false effect.typ])

let pure : t =
  { effect = false; typ = Type.Pure }

let function_typ (args : (Name.t * Type'.t) list) (body_effect : t) : Type.t =
  match args with
  | [] ->
    if body_effect.effect then
      failwith "Unexpected effect."
    else
      body_effect.typ
  | _ :: args ->
    List.fold_left (fun effect_typ _ -> Type.Arrow (false, effect_typ))
      (Type.Arrow (body_effect.effect, body_effect.typ))
      args

let unify (effects : t list) : t =
  { effect = List.exists (fun effect -> effect.effect) effects;
    typ = Type.unify (List.map (fun effect -> effect.typ) effects) }

let monadise (typ : Type'.t) (effect : t) : Type'.t =
  let typ = Type.monadise typ effect.typ in
  if effect.effect then
    Type'.Monad typ
  else
    typ