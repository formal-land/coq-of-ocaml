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
  type t = Type.t PathName.Map.t

  let pp (effects : t) : SmartPrint.t =
    PathName.Map.bindings effects |> OCaml.list (fun (x, typ) ->
      nest (PathName.pp x ^^ !^ ":" ^^ Type.pp false typ))

  let in_function (path : PathName.Path.t) (effects : t)
    (args : (Name.t * Type'.t) list) : t =
    List.fold_left (fun effects (x, _) ->
      PathName.Map.add (PathName.of_name path x) Type.Pure effects)
      effects args
end

type t = { effect : bool; typ : Type.t }

let pure : t =
  { effect = false; typ = Type.Pure }

let function_typ (args : (Name.t * Type'.t) list) (body_effect : t) : Type.t =
  match args with
  | [] -> failwith "Expected some arguments."
  | _ :: args ->
    List.fold_left (fun effect_typ _ -> Type.Arrow (false, effect_typ))
      (Type.Arrow (body_effect.effect, body_effect.typ))
      args

let monadise (typ : Type'.t) (effect : t) : Type'.t =
  let typ = Type.monadise typ effect.typ in
  if effect.effect then
    Type'.Monad typ
  else
    typ