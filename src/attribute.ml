(** The OCaml attributes to customize the Coq generation. *)
open Monad.Notations

type t =
  | AxiomWithReason
  | Cast
  | DisableExistential
  | ForceGadt
  | TaggedGadt
  | Implicit of string
  | MatchGadt
  | MatchGadtWithResult
  | MatchWithDefault
  | MutualAsNotation
  | Phantom
  | PlainModule
  | Struct of string
  | TaggedMatch
  | TypAnnotation

let of_payload_string
  (error_message : string) (id : string) (payload : Parsetree.payload)
  : string Monad.t =
  match payload with
  | Parsetree.PStr [{
      pstr_desc =
        Pstr_eval (
          {
            pexp_desc = Pexp_constant (Pconst_string (payload, _, _));
            _
          },
          _
        );
      _
    }] -> return payload
  | _ ->
    let message = "missing_string_for_attribute " ^ id in
    raise
      message
      Unexpected
      (
        "Expected a single string parameter for this attribute.\n\n" ^
        error_message
      )

let of_attributes (attributes : Typedtree.attributes) : t list Monad.t =
  attributes |> Monad.List.filter_map (
    fun {Parsetree.attr_name; attr_payload; _} ->
    set_loc attr_name.Asttypes.loc (
    let id = attr_name.Asttypes.txt in
    match id with
    | "coq_axiom" ->
      raise
        None
        Unexpected
        "Depreacated attribute. Use @coq_axiom_with_reason instead."
    | "coq_axiom_with_reason" ->
      let error_message = "Give a reason for this axiom" in
      let* _ = of_payload_string error_message id attr_payload in
      return (Some AxiomWithReason)
    | "coq_cast" -> return (Some Cast)
    | "coq_disable_existential" -> return (Some DisableExistential)
    | "coq_force_gadt" -> return (Some ForceGadt)
    | "coq_tag_gadt" -> return (Some TaggedGadt)
    | "coq_implicit" ->
      let error_message =
        "Give a value such as \"(A := unit)\" to define an implicit type" in
      let* payload = of_payload_string error_message id attr_payload in
      return (Some (Implicit payload))
    | "coq_match_gadt" -> return (Some MatchGadt)
    | "coq_match_gadt_with_result" -> return (Some MatchGadtWithResult)
    | "coq_match_with_default" -> return (Some MatchWithDefault)
    | "coq_mutual_as_notation" -> return (Some MutualAsNotation)
    | "coq_plain_module" -> return (Some PlainModule)
    | "coq_phantom" -> return (Some Phantom)
    | "coq_struct" ->
      let error_message = "Give the name of the parameter to recurse on" in
      let* payload = of_payload_string error_message id attr_payload in
      return (Some (Struct payload))
    | "coq_type_annotation" -> return (Some TypAnnotation)
    | "coq_tagged_match" -> return (Some TaggedMatch)
    | _ -> return None)
  )

let has_axiom_with_reason (attributes : t list) : bool =
  attributes |> List.exists (function
    | AxiomWithReason -> true
    | _ -> false
  )

let has_cast (attributes : t list) : bool =
  attributes |> List.exists (function
    | Cast -> true
    | _ -> false
  )

let has_disable_existential (attributes : t list) : bool =
  attributes |> List.exists (function
    | DisableExistential -> true
    | _ -> false
  )

let has_force_gadt (attributes : t list) : bool =
  attributes |> List.exists (function
    | ForceGadt -> true
    | _ -> false
  )

let get_implicits (attributes : t list) : string list =
  attributes |> Util.List.filter_map (function
    | Implicit implicit -> Some implicit
    | _ -> None
  )

let has_match_gadt (attributes : t list) : bool =
  attributes |> List.exists (function
    | MatchGadt -> true
    | _ -> false
  )

let has_match_gadt_with_result (attributes : t list) : bool =
  attributes |> List.exists (function
    | MatchGadtWithResult -> true
    | _ -> false
  )

let has_match_with_default (attributes : t list) : bool =
  attributes |> List.exists (function
    | MatchWithDefault -> true
    | _ -> false
  )

let has_mutual_as_notation (attributes : t list) : bool =
  attributes |> List.exists (function
    | MutualAsNotation -> true
    | _ -> false
  )

let has_phantom (attributes : t list) : bool =
  attributes |> List.exists (function
    | Phantom -> true
    | _ -> false
  )

let has_plain_module (attributes : t list) : bool =
  attributes |> List.exists (function
    | PlainModule -> true
    | _ -> false
  )

let has_tagged_match (attributes : t list) : bool =
  attributes |> List.exists (function
    | TaggedMatch -> true
    | _ -> false
  )

let has_tag_gadt (attributes : t list) : bool =
  attributes |> List.exists (function
    | TaggedGadt -> true
    | _ -> false
  )

(** We compute the existence of this attribute outside of the monad for
   performance reasons. *)
let has_precise_signature (attributes : Typedtree.attributes) : bool =
  attributes |> List.exists (fun {Parsetree.attr_name; _} ->
    let id = attr_name.Asttypes.txt in
    match id with
    | "coq_precise_signature" -> true
    | _ -> false
  )

let get_structs (attributes : t list) : string list =
  attributes |> Util.List.filter_map (function
    | Struct name -> Some name
    | _ -> None
  )

let has_typ_annotation (attributes : t list) : bool =
  attributes |> List.exists (function
    | TypAnnotation -> true
    | _ -> false
  )
