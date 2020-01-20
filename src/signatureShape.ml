(** The shape of a signature to simplify comparisons. Two signatures are
    considered similar if they have the same shape. The shape only contains the
    names of values and sub-module at the top-level of the module. Basically,
    shapes are lists of strings. *)
open SmartPrint

type t = Name.t list

let of_signature (signature : Types.signature) : t =
  signature |> Util.List.filter_map (fun item ->
    match item with
    | Types.Sig_value (ident, _) -> Some (Name.of_ident true ident)
    | Sig_module (ident, _, _) -> Some (Name.of_ident false ident)
    | _ -> None
  )

let are_equal (shape1 : t) (shape2 : t) : bool =
  Name.Set.equal (Name.Set.of_list shape1) (Name.Set.of_list shape2)

let pretty_print (shape : t) : SmartPrint.t =
  shape |> OCaml.list Name.to_coq
