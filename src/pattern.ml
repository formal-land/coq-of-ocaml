(** Patterns used for the "match". *)
open Typedtree
open SmartPrint
open Monad.Notations

type t =
  | Any
  | Constant of Constant.t
  | Variable of Name.t
  | Tuple of t list
  | Constructor of PathName.t * t list (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * Name.t
  | Record of (PathName.t * t) list (** A list of fields from a record with their expected patterns. *)
  | Or of t * t

(** Import an OCaml pattern. If the answer is [None] then the pattern is
    impossible (for example with extensible types). *)
let rec of_pattern (p : pattern) : t option Monad.t =
  set_loc (Loc.of_location p.pat_loc) (
  match p.pat_desc with
  | Tpat_any -> return (Some Any)
  | Tpat_var (x, _) -> return (Some (Variable (Name.of_ident true x)))
  | Tpat_tuple ps ->
    Monad.List.map of_pattern ps >>= fun patterns ->
    return (
      let patterns = Util.Option.all patterns in
      Util.Option.map patterns (fun patterns ->
      Tuple patterns)
    )
  | Tpat_construct (_, constructor_description, ps) ->
    begin match constructor_description.cstr_tag with
    | Cstr_extension _ ->
      raise
        None
        NotSupported
        "Patterns of extensible types are not handled"
    | _ ->
      let x = PathName.of_constructor_description constructor_description in
      Monad.List.map of_pattern ps >>= fun patterns ->
      return (
        let patterns = Util.Option.all patterns in
        Util.Option.map patterns (fun patterns ->
        Constructor (x, patterns))
      )
    end
  | Tpat_alias (p, x, _) ->
    of_pattern p >>= fun pattern ->
    return (
      Util.Option.map pattern (fun pattern ->
      Alias (pattern, Name.of_ident true x))
    )
  | Tpat_constant c ->
    Constant.of_constant c >>= fun constant ->
    return (Some (Constant constant))
  | Tpat_variant (label, p, _) ->
    let path_name = PathName.of_variant label in
    (match p with
    | None -> return (Some [])
    | Some p ->
      of_pattern p >>= fun pattern ->
      return (
        Util.Option.map pattern (fun pattern ->
        [pattern])
      )
    ) >>= fun patterns ->
    raise
      (Util.Option.map patterns (fun patterns ->
      Constructor (path_name, patterns)))
      NotSupported
      "Patterns on variants are not supported"
  | Tpat_record (fields, _) ->
    (fields |> Monad.List.map (fun (_, label_description, p) ->
      let x = PathName.of_label_description label_description in
      of_pattern p >>= fun pattern ->
      return (
        Util.Option.map pattern (fun pattern -> (x, pattern))
      )
    )) >>= fun fields ->
    return (
      Util.Option.map (Util.Option.all fields) (fun fields ->
      Record fields)
    )
  | Tpat_array ps ->
    Monad.List.map of_pattern ps >>= fun patterns ->
    raise
      (
        Util.Option.map (Util.Option.all patterns) (fun patterns ->
        Tuple patterns)
      )
      NotSupported
      "Patterns on array are not supported"
  | Tpat_or (p1, p2, _) ->
    of_pattern p1 >>= fun pattern1 ->
    of_pattern p2 >>= fun pattern2 ->
    return (
      Util.Option.bind pattern1 (fun pattern1 ->
      Util.Option.map pattern2 (fun pattern2 ->
      Or (pattern1, pattern2)))
    )
  | Tpat_lazy p ->
    of_pattern p >>= fun pattern ->
    raise pattern NotSupported "Lazy patterns are not supported")

let rec flatten_or (p : t) : t list =
  match p with
  | Or (p1, p2) -> flatten_or p1 @ flatten_or p2
  | _ -> [p]

(** Pretty-print a pattern to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (p : t) : SmartPrint.t =
  match p with
  | Any -> !^ "_"
  | Constant c -> Constant.to_coq c
  | Variable x -> Name.to_coq x
  | Tuple ps ->
    if ps = [] then
      !^ "tt"
    else
      parens @@ nest @@ separate (!^ "," ^^ space) (List.map (to_coq false) ps)
  | Constructor (x, ps) ->
    if ps = [] then
      if PathName.is_tt x then !^ "_" else PathName.to_coq x
    else
      Pp.parens paren @@ nest @@ separate space (PathName.to_coq x :: List.map (to_coq true) ps)
  | Alias (p, x) ->
    Pp.parens paren @@ nest (to_coq true p ^^ !^ "as" ^^ Name.to_coq x)
  | Record fields ->
    !^ "{|" ^^
    nest_all @@ separate (!^ ";" ^^ space) (fields |> List.map (fun (x, p) ->
      nest (PathName.to_coq x ^^ !^ ":=" ^^ to_coq false p)))
    ^^ !^ "|}"
  | Or _ ->
    let ps = flatten_or p in
    Pp.parens paren @@ group (
      separate (space ^^ !^ "|" ^^ space) (ps |> List.map (to_coq false))
    )
