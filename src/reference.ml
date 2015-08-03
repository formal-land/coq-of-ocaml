open Typedtree
open SmartPrint

type t = {
  name : Name.t;
  typ : Type.t }

let pp (r : t) : SmartPrint.t =
  nest (!^ "Reference" ^^ OCaml.tuple [Name.pp r.name; Type.pp r.typ])

let is_reference (loc : Loc.t) (cases : value_binding list) : bool =
  match cases with
  | [{ vb_expr = {
    exp_desc = Texp_apply ({exp_desc = Texp_ident (path, _, _)}, [_]) }}]
    when PathName.of_path loc path = PathName.of_name ["Pervasives"] "ref" ->
    true
  | _ -> false

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t) (cases : value_binding list)
  : t =
  match cases with
  | [{ vb_pat = { pat_desc = Tpat_var (x, _) };
    vb_expr = { exp_type = {Types.desc = Types.Tconstr (_, [typ], _) }}}] ->
    { name = Name.of_ident x;
      typ = Type.of_type_expr env loc typ }
  | _ -> Error.raise loc "This kind of reference definition is not handled."

let update_env (r : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  env
  |> FullEnvi.add_var [] ("read_" ^ r.name) ()
  |> FullEnvi.add_var [] ("write_" ^ r.name) ()
  |> FullEnvi.add_descriptor [] r.name

let update_env_with_effects (r : t) (env : Effect.Type.t FullEnvi.t)
  (id : Effect.Descriptor.Id.t) : Effect.Type.t FullEnvi.t =
  let env = FullEnvi.add_descriptor [] r.name env in
  let effect_typ =
    Effect.Type.Arrow (
      Effect.Descriptor.singleton
        id
        (Envi.bound_name Loc.Unknown (PathName.of_name [] r.name) env.FullEnvi.descriptors),
      Effect.Type.Pure) in
  env
  |> FullEnvi.add_var [] ("read_" ^ r.name) effect_typ
  |> FullEnvi.add_var [] ("write_" ^ r.name) effect_typ

let to_coq (r : t) : SmartPrint.t =
  !^ "Definition" ^^ Name.to_coq r.name ^^ !^ ":=" ^^
    !^ "Effect.make" ^^ Type.to_coq true r.typ ^^ !^ "Empty_set" ^-^ !^ "." ^^
  newline ^^ newline ^^
  !^ "Definition" ^^ Name.to_coq ("read_" ^ r.name) ^^ !^ "(_ : unit)" ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ Name.to_coq r.name ^^ !^ "]" ^^ Type.to_coq true r.typ ^^ !^ ":=" ^^
  newline ^^ indent (
    !^ "fun s => (inl (fst s), s).") ^^
  newline ^^ newline ^^
  !^ "Definition" ^^ Name.to_coq ("write_" ^ r.name) ^^
    parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false r.typ) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ Name.to_coq r.name ^^ !^ "]" ^^ !^ "unit" ^^ !^ ":=" ^^
  newline ^^ indent (
    !^ "fun s => (inl tt, (x, tt)).")
