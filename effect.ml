(** Types for the effects. *)
open SmartPrint

module Type' = Type

module Type = struct
  type t =
    | Ground
    | Arrow of bool * t * t

  let rec pp (paren : bool) (typ : t) : SmartPrint.t =
    match typ with
    | Ground -> !^ "."
    | Arrow (effect, typ1, typ2) -> Pp.parens paren @@ nest (
      pp true typ1 ^^ (if effect then !^ "-e->" else !^ "->") ^^ pp false typ2)

  let rec is_pure (typ : t) : bool =
    match typ with
    | Ground -> true
    | Arrow (effect, typ1, typ2) -> not effect && is_pure typ1 && is_pure typ2

  (** The effect type of [typ], supposing [typ] to be effect-free. *)
  let rec of_type (typ : Type.t) : t =
    match typ with
    | Type.Variable _ | Type.Tuple _ | Type.Apply _ -> Ground
    | Type.Arrow (typ1, typ2) -> Arrow (false, of_type typ1, of_type typ2)
    | Type.Monad _ -> failwith "Monadic type unexpected."

  let rec monadise (typ : Type.t) (effect_typ : t) : Type.t =
    match (typ, effect_typ) with
    | (Type.Variable _, Ground) | (Type.Tuple _, Ground) | (Type.Apply _, Ground) -> typ
    | (Type.Arrow (typ1, typ2), Arrow (effect, effect_typ1, effect_typ2)) ->
      let typ1 = monadise typ1 effect_typ1 in
      let typ2 = monadise typ2 effect_typ2 in
      Type.Arrow (typ1, if effect then Type.Monad typ2 else typ2)
    | (Type.Monad _, _) -> failwith "This type is already monadic."
    | _ ->
      failwith "Type and effect type are not compatible."
end

module Env = struct
  type t = Type.t PathName.Map.t

  let pp (effects : t) : SmartPrint.t =
    PathName.Map.bindings effects |> OCaml.list (fun (x, typ) ->
      nest (PathName.pp x ^^ !^ ":" ^^ Type.pp false typ))

  let in_function (path : PathName.Path.t) (effects : t)
    (args : (Name.t * Type'.t) list) : t =
    List.fold_left (fun effects (x, x_typ) ->
      PathName.Map.add (PathName.of_name path x) (Type.of_type x_typ) effects)
      effects args
end

type t = { effect : bool; typ : Type.t }

let pure : t =
  { effect = false; typ = Type.Ground }

let function_typ (args : (Name.t * Type'.t) list) (body_effect : t) : Type.t =
  match List.rev args with
  | [] ->
    if body_effect.effect then
      failwith "Unexpected effect."
    else
      body_effect.typ
  | (_, x_typ) :: args ->
    List.fold_left (fun effect_typ (_, x_typ) ->
      Type.Arrow (false, Type.of_type x_typ, effect_typ))
      (Type.Arrow (body_effect.effect, Type.of_type x_typ, body_effect.typ))
      args

let monadise (typ : Type'.t) (effect : t) : Type'.t =
  let typ = Type.monadise typ effect.typ in
  if effect.effect then
    Type'.Monad typ
  else
    typ