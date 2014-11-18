(** Types for the effects. *)
open SmartPrint

module Descriptor = struct
  module Id = struct
    type t =
      | Ether of PathName.t
      | Loc of Loc.t
  end
  module Map = Map.Make (struct type t = Id.t let compare = compare end)
  type t = BoundName.t Map.t

  let pp (d : t) : SmartPrint.t =
    OCaml.list (fun (_, x) -> BoundName.pp x) (Map.bindings d)

  let pure : t = Map.empty

  let is_pure (d : t) : bool =
    Map.is_empty d

  let eq (d1 : t) (d2 : t) : bool =
    Map.equal (fun _ _ -> true) d1 d2

  let singleton (id : Id.t) (x : BoundName.t) : t =
    Map.singleton id x

  let union (ds : t list) : t =
    List.fold_left (fun d1 d2 -> Map.fold Map.add d1 d2) pure ds

  let mem (x : BoundName.t) (d : t) : bool =
    Map.exists (fun _ y -> x = y) d

  let remove (x : BoundName.t) (d : t) : t =
    Map.filter (fun _ y -> x <> y) d

  let elements (d : t) : BoundName.t list =
    List.map snd (Map.bindings d)

  let index (x : BoundName.t) (d : t) : int =
    let rec find_index l f =
      match l with
      | [] -> 0
      | x :: xs -> if f x then 0 else 1 + find_index xs f in
    find_index (Map.bindings d) (fun (_, y) -> y = x)

  let to_coq (d : t) : SmartPrint.t =
    OCaml.list (fun (_, x) -> BoundName.to_coq x) (Map.bindings d)

  let subset_to_coq (d1 : t) (d2 : t) : SmartPrint.t =
    let rec aux xs1 xs2 : bool list =
      match (xs1, xs2) with
      | ([], _) -> List.map (fun _ -> false) xs2
      | (x1 :: xs1', x2 :: xs2') ->
        if x1 = x2 then
          true :: aux xs1' xs2'
        else
          false :: aux xs1 xs2'
      | (_ :: _, []) ->
        failwith "Must be a subset to display the subset." in
    let bs = aux (Map.bindings d1) (Map.bindings d2) in
    brakets (separate (!^ ";") (List.map (fun _ -> !^ "_") bs)) ^^
    double_quotes (separate empty
      (List.map (fun b -> if b then !^ "1" else !^ "0") bs))

  let depth_lift (d : t) : t =
    Map.map BoundName.depth_lift d

  let leave_prefix (name : Name.t) (d : t) : t =
    Map.map (fun x -> BoundName.leave_prefix name x) d
end

module Type = struct
  type t =
    | Pure
    | Arrow of Descriptor.t * t

  let rec pp (typ : t) : SmartPrint.t =
    match typ with
    | Pure -> !^ "."
    | Arrow (d, typ) -> nest (
      !^ "." ^^
      (if Descriptor.is_pure d then
        !^ "->"
      else
        !^ "-" ^-^ Descriptor.pp d ^-^ !^ "->") ^^
      pp typ)

  let rec is_pure (typ : t) : bool =
    match typ with
    | Pure -> true
    | Arrow (d, typ) -> Descriptor.is_pure d && is_pure typ

  let rec compress (typ : t) : t =
    if is_pure typ then
      Pure
    else
      match typ with
      | Pure -> Pure
      | Arrow (d, typ) -> Arrow (d, compress typ)

  let rec eq (typ1 : t) (typ2 : t) : bool =
    match (typ1, typ2) with
    | (Pure, _) -> is_pure typ2
    | (_, Pure) -> is_pure typ1
    | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
      (Descriptor.eq d1 d2) && eq typ1 typ2

  let rec return_descriptor (typ : t) (nb_args : int) : Descriptor.t =
    if nb_args = 0 then
      Descriptor.pure
    else
      match typ with
      | Pure -> Descriptor.pure
      | Arrow (d, typ) ->
        Descriptor.union [d; return_descriptor typ (nb_args - 1)]

  let rec return_type (typ : t) (nb_args : int) : t =
    if nb_args = 0 then
      typ
    else
      match typ with
      | Pure -> Pure
      | Arrow (_, typ) -> return_type typ (nb_args - 1)

  let union (typs : t list) : t =
    let rec aux typ1 typ2 =
      match (typ1, typ2) with
      | (Pure, _) -> if is_pure typ2 then Pure else typ2
      | (_, Pure) -> if is_pure typ1 then Pure else typ1
      | (Arrow (d1, typ1), Arrow (d2, typ2)) ->
        Arrow (Descriptor.union [d1; d2], aux typ1 typ2) in
    List.fold_left aux Pure typs

  let rec depth_lift (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (d, typ) -> Arrow (Descriptor.depth_lift d, depth_lift typ)

  let rec leave_prefix (x : Name.t) (typ : t) : t =
    match typ with
    | Pure -> Pure
    | Arrow (d, typ) -> Arrow (Descriptor.leave_prefix x d, leave_prefix x typ)
end

type t = { descriptor : Descriptor.t; typ : Type.t }

let pp (effect : t) : SmartPrint.t =
  nest (!^ "Effect" ^^ OCaml.tuple [
    Descriptor.pp effect.descriptor; Type.pp effect.typ])

let function_typ (args : 'a list) (body_effect : t) : Type.t =
  match args with
  | [] -> body_effect.typ
  | _ :: args ->
    List.fold_left (fun effect_typ _ ->
      Type.Arrow (Descriptor.pure, effect_typ))
      (Type.Arrow
          (body_effect.descriptor, body_effect.typ))
      args

let pure : t = {
  descriptor = Descriptor.pure;
  typ = Type.Pure }

let union (effects : t list) : t =
  { descriptor =
      Descriptor.union @@ List.map (fun effect -> effect.descriptor) effects;
    typ = Type.union (List.map (fun effect -> effect.typ) effects) }  