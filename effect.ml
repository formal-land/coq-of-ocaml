(** Types for the effects. *)
module Type' = Type

module Type = struct
  type t =
    | Ground
    | Arrow of bool * t

  let rec is_pure (typ : t) : bool =
    match typ with
    | Ground -> true
    | Arrow (effect, typ) -> not effect && is_pure typ

  (** Supposes [typ] to be pure. *)
  let rec of_type (typ : Type.t) : t =
    match typ with
    | Type.Variable _ | Type.Tuple _ | Type.Apply _ -> Ground
    | Type.Arrow (_, typ) -> Arrow (false, of_type typ)
    | Type.Monad _ -> failwith "Monadic type unexpected."

  let rec monadise (typ : Type.t) (effect_typ : t) : Type.t =
  match (typ, effect_typ) with
  | (Type.Variable _, Ground) | (Type.Tuple _, Ground) | (Type.Apply _, Ground) -> typ
  | (Type.Arrow (typ1, typ2), Arrow (effect, effect_typ2)) ->
    let typ2 = monadise typ2 effect_typ2 in
    Type.Arrow (typ1, if effect then Type.Monad typ2 else typ2)
  | (Type.Monad _, _) -> failwith "This type is already monadic."
  | _ -> failwith "Type and effect type are not compatible."
end

type t = { effect : bool; typ : Type.t }

let pure : t =
  { effect = false; typ = Type.Ground }

let monadise (typ : Type'.t) (effect : t) : Type'.t=
  let typ = Type.monadise typ effect.typ in
  if effect.effect then
    Type'.Monad typ
  else
    typ