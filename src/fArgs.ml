open SmartPrint
(** The type to represent functor arguments. *)

type t = int option
(** [None] when there are no FArgs, or [Some] with the number of free type
    variables in the functor parameters. *)

let to_coq (fargs : t) : SmartPrint.t =
  match fargs with Some _ -> !^"`{FArgs}" | None -> empty

(** Print underscores for the number of implicit parameters introduced by the
    [`{FArgs}] notation. *)
let to_coq_underscores (fargs : t) : SmartPrint.t list =
  match fargs with
  | Some nb_free_vars -> Pp.n_underscores (nb_free_vars + 1)
  | None -> []
