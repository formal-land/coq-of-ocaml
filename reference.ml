open SmartPrint

type t = {
  name : Name.t;
  typ : Type.t }

let pp (r : t) : SmartPrint.t =
  nest (!^ "Reference" ^^ OCaml.tuple [Name.pp r.name; Type.pp r.typ])

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
    !^ "Effect.make" ^^ Type.to_coq true r.typ ^^ !^ "unit" ^-^ !^ "." ^^
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