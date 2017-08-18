open Typedtree
open SmartPrint

type t = {
  name : Name.t;
  typ : Type.t }

let pp (exn : t) : SmartPrint.t =
  nest (!^ "Exception" ^^ OCaml.tuple [Name.pp exn.name; Type.pp exn.typ])

let of_ocaml (env : unit FullEnvi.t) (loc : Loc.t)
  (exn : extension_constructor) : t =
  let name = Name.of_ident exn.ext_id in
  let typs =
    match exn.ext_type.Types.ext_args with
    | Types.Cstr_tuple typs -> typs
    | Types.Cstr_record _ -> Error.raise loc "Unhandled named constructor parameters." in
  let typ = Type.Tuple (typs |> List.map (fun typ -> Type.of_type_expr env loc typ)) in
  { name = name; typ = typ}

let update_env (exn : t) (env : unit FullEnvi.t) : unit FullEnvi.t =
  FullEnvi.add_exception [] exn.name env

let update_env_with_effects (exn : t) (env : Effect.Type.t FullEnvi.t)
  (id : Effect.Descriptor.Id.t) : Effect.Type.t FullEnvi.t =
  FullEnvi.add_exception_with_effects [] exn.name id env

let to_coq (exn : t) : SmartPrint.t =
  !^ "Definition" ^^ Name.to_coq exn.name ^^ !^ ":=" ^^
    !^ "Effect.make" ^^ !^ "unit" ^^ Type.to_coq true exn.typ ^-^ !^ "." ^^
  newline ^^ newline ^^
  !^ "Definition" ^^ Name.to_coq ("raise_" ^ exn.name) ^^ !^ "{A : Type}" ^^
    nest (parens (!^ "x" ^^ !^ ":" ^^ Type.to_coq false exn.typ)) ^^ !^ ":" ^^
    !^ "M" ^^ !^ "[" ^^ Name.to_coq exn.name ^^ !^ "]" ^^ !^ "A" ^^ !^ ":=" ^^
  newline ^^ indent (
    !^ "fun s => (inr (inl x), s).")
