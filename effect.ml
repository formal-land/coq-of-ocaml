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