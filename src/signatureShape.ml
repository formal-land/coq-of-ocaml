(** The shape of a signature to simplify comparisons. Two signatures are
    considered similar if they have the same shape. The shape only contains the
    names of values and sub-module at the top-level of the module. Basically,
    shapes are sets of strings. *)
open SmartPrint

type t = Name.Set.t

(** A hash to optimize the computation of shapes. *)
module Hash = Hashtbl.Make (struct
  type t = Types.signature
  let equal = (==)
  let hash = Hashtbl.hash
end)

let signature_shape_hash : t Hash.t =
  Hash.create 12

let of_signature (signature : Types.signature) : t =
  match Hash.find_opt signature_shape_hash signature with
  | None ->
    let shape_list =
      signature |> Util.List.filter_map (fun item ->
        match item with
        | Types.Sig_value (ident, _) -> Some (Name.of_ident true ident)
        | Sig_module (ident, _, _) -> Some (Name.of_ident false ident)
        | _ -> None
      ) in
    let shape = Name.Set.of_list shape_list in
    Hash.add signature_shape_hash signature shape;
    shape
  | Some shape -> shape

let are_equal : t -> t -> bool = Name.Set.equal

let pretty_print (shape : t) : SmartPrint.t =
  shape
  |> Name.Set.elements
  (* We sort the elements of the shape to have a canonical representation. *)
  |> List.sort compare
  |> OCaml.list Name.to_coq
