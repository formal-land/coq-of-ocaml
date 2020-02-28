(** The OCaml attributes to customize the Coq generation. *)
open Monad.Notations

type t =
  | Axiom
  | ForceGadt
  | Implicit of string
  | MatchGadt
  | MatchGadtWithResult
  | MatchWithDefault

let of_attributes (attributes : Typedtree.attributes) : t list Monad.t =
  attributes |> Monad.List.filter_map (fun (loc, payload) ->
    set_loc (Loc.of_location loc.Asttypes.loc) (
    let id = loc.Asttypes.txt in
    match id with
    | "coq_axiom" -> return (Some Axiom)
    | "coq_force_gadt" -> return (Some ForceGadt)
    | "coq_implicit" ->
      begin match payload with
      | Parsetree.PStr [{
          pstr_desc =
            Pstr_eval (
              {
                pexp_desc = Pexp_constant (Pconst_string (implicit, _));
                _
              },
              _
            );
          _
        }] ->
        return (Some (Implicit implicit))
      | _ ->
        raise None Unexpected "Expected a single string parameter for attribute"
      end
    | "coq_match_gadt" -> return (Some MatchGadt)
    | "coq_match_gadt_with_result" -> return (Some MatchGadtWithResult)
    | "coq_match_with_default" -> return (Some MatchWithDefault)
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
