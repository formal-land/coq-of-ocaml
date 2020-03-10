(** The OCaml attributes to customize the Coq generation. *)
open Monad.Notations

type t =
  | Axiom
  | ForceGadt
  | Implicit of string
  | MatchGadt
  | MatchGadtWithResult
  | MatchWithDefault
  | Struct of string

let of_payload_string (id : string) (payload : Parsetree.payload)
  : string Monad.t =
  match payload with
  | Parsetree.PStr [{
      pstr_desc =
        Pstr_eval (
          {
            pexp_desc = Pexp_constant (Pconst_string (payload, _));
            _
          },
          _
        );
      _
    }] -> return payload
  | _ ->
    let message = "missing_string_for_attribute " ^ id in
    raise message Unexpected "Expected a single string parameter this attribute"

let of_attributes (attributes : Typedtree.attributes) : t list Monad.t =
  attributes |> Monad.List.filter_map (fun (loc, payload) ->
    set_loc (Loc.of_location loc.Asttypes.loc) (
    let id = loc.Asttypes.txt in
    match id with
    | "coq_axiom" -> return (Some Axiom)
    | "coq_force_gadt" -> return (Some ForceGadt)
    | "coq_implicit" ->
      of_payload_string id payload >>= fun payload ->
      return (Some (Implicit payload))
    | "coq_match_gadt" -> return (Some MatchGadt)
    | "coq_match_gadt_with_result" -> return (Some MatchGadtWithResult)
    | "coq_match_with_default" -> return (Some MatchWithDefault)
    | "coq_struct" ->
      of_payload_string id payload >>= fun payload ->
      return (Some (Struct payload))
    | _ -> return None)
  )

let has_axiom (attributes : t list) : bool =
  attributes |> List.exists (function
    | Axiom -> true
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

let get_structs (attributes : t list) : string list =
  attributes |> Util.List.filter_map (function
    | Struct name -> Some name
    | _ -> None
  )
