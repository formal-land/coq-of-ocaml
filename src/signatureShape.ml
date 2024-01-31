open SmartPrint
(** The shape of a signature to simplify comparisons. Two signatures are
    considered similar if they have the same shape. The shape only contains the
    names of values and sub-module at the top-level of the module. Basically,
    shapes are sets of strings. *)

(** With the precise mode, we compute a type shape for the values of the
    signature. This type shape helps to distinguish between two signatures with
    the same elements but different types. We can activate this mode with the
    attribute `[@@coq_precise_signature]` on a signature definition. *)
module TypeShape = struct
  type t = { nb_function_parameters : int; nb_type_applications_result : int }

  let rec get_nb_function_parameters (typ : Types.type_expr) :
      int * Types.type_expr =
    match Types.get_desc typ with
    | Tarrow (_, _, typ2, _) ->
        let nb_function_parameters, result_typ =
          get_nb_function_parameters typ2
        in
        (nb_function_parameters + 1, result_typ)
    | _ -> (0, typ)

  let rec get_nb_type_applications (typ : Types.type_expr) : int =
    match Types.get_desc typ with
    | Tconstr (_, [ typ ], _) -> 1 + get_nb_type_applications typ
    | _ -> 0

  let of_typ (typ : Types.type_expr) : t =
    let nb_function_parameters, result_typ = get_nb_function_parameters typ in
    {
      nb_function_parameters;
      nb_type_applications_result = get_nb_type_applications result_typ;
    }
end

type t = {
  high_level : Name.Set.t;
  precise : TypeShape.t option Name.Map.t option;
}

let of_signature (attributes : Typedtree.attributes option)
    (signature : Types.signature) : t =
  let shape_list =
    signature
    |> List.filter_map (fun item ->
           match item with
           | Types.Sig_value (ident, typ, _) ->
               let typ_shape = TypeShape.of_typ typ.val_type in
               Some (Name.of_ident_raw ident, Some typ_shape)
           | Sig_module (ident, _, _, _, _) ->
               Some (Name.of_ident_raw ident, None)
           | _ -> None)
  in
  let high_level =
    shape_list |> List.map (fun (name, _) -> name) |> Name.Set.of_list
  in
  let compute_precise =
    match attributes with
    | None -> true
    | Some attributes -> Attribute.has_precise_signature attributes
  in
  let precise =
    if compute_precise then Some (shape_list |> List.to_seq |> Name.Map.of_seq)
    else None
  in
  { high_level; precise }

let are_equal (shape1 : t) (shape2 : t) : bool =
  Name.Set.equal shape1.high_level shape2.high_level
  &&
  match (shape1.precise, shape2.precise) with
  | Some precise1, Some precise2 -> Name.Map.equal ( = ) precise1 precise2
  | _ -> true

let is_empty (shape : t) : bool = Name.Set.is_empty shape.high_level

let pretty_print (shape : t) : SmartPrint.t =
  shape.high_level |> Name.Set.elements
  (* We sort the elements of the shape to have a canonical representation. *)
  |> List.sort compare
  |> OCaml.list Name.to_coq
