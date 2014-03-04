(** Types for the effects. *)
open SmartPrint

module Atom = struct
  module Kind = struct
    type t = State | Error

    let pp (kind : t) : SmartPrint.t =
      match kind with
      | State -> !^ "State"
      | Error -> !^ "Error"
  end

  type t = {
    kind : Kind.t;
    coq_type : SmartPrint.t }

  let pp (a : t) : SmartPrint.t =
    nest (!^ "Atom" ^^ OCaml.tuple [Kind.pp a.kind; a.coq_type])
end

module Descriptor = struct
  type t = PathName.Set.t

  let pp (d : t) : SmartPrint.t =
    OCaml.list PathName.pp (PathName.Set.elements d)

  let pure : t = PathName.Set.empty

  let is_pure (d : t) : bool =
    PathName.Set.is_empty d

  let eq (d1 : t) (d2 : t) : bool =
    PathName.Set.equal d1 d2

  let singleton (x : PathName.t) : t =
    PathName.Set.singleton x

  let union (ds : t list) : t =
    List.fold_left (PathName.Set.union) pure ds

  let to_coq (d : t) : SmartPrint.t =
    OCaml.list PathName.to_coq (PathName.Set.elements d)

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
    let bs = aux (PathName.Set.elements d1) (PathName.Set.elements d2) in
    brakets (separate (!^ ";") (List.map (fun _ -> !^ "_") bs)) ^^
    double_quotes (separate empty
      (List.map (fun b -> if b then !^ "1" else !^ "0") bs))
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

type t = { descriptor : Descriptor.t; typ : Type.t }

let pp (effect : t) : SmartPrint.t =
  nest (!^ "Effect" ^^ OCaml.tuple [
    Descriptor.pp effect.descriptor; Type.pp false effect.typ])

let function_typ (args_names : Name.t list) (body_effect : t) : Type.t =
  match args_names with
  | [] -> body_effect.typ
  | _ :: args_names ->
    List.fold_left (fun effect_typ _ ->
      Type.Arrow (Descriptor.pure, effect_typ))
      (Type.Arrow
          (body_effect.descriptor, body_effect.typ))
      args_names

let union (effects : t list) : t =
  { descriptor =
      Descriptor.union @@ List.map (fun effect -> effect.descriptor) effects;
    typ = Type.union (List.map (fun effect -> effect.typ) effects) }