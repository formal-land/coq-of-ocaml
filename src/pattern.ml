open Typedtree
(** Patterns used for the "match". *)

open SmartPrint
open Monad.Notations

type t =
  | Any
  | Constant of Constant.t
  | Variable of Name.t
  | Tuple of t list
  | Constructor of PathName.t * t list
      (** A constructor name and a list of pattern in arguments. *)
  | Alias of t * Name.t
  | Record of (PathName.t * t) list
      (** A list of fields from a record with their expected patterns. *)
  | Or of t * t

(** Import an OCaml pattern. If the answer is [None] then the pattern is
    impossible (for example with extensible types). *)
let rec of_pattern :
    type pattern_kind. pattern_kind general_pattern -> t option Monad.t =
 fun p ->
  set_loc p.pat_loc
    (match p.pat_desc with
    | Tpat_any -> return (Some Any)
    | Tpat_var (x, _) ->
        Name.of_ident true x >>= fun x -> return (Some (Variable x))
    | Tpat_tuple ps ->
        Monad.List.map of_pattern ps >>= fun patterns ->
        return
          (let patterns = Util.Option.all patterns in
           patterns |> Option.map (fun patterns -> Tuple patterns))
    | Tpat_construct (_, constructor_description, ps, _) -> (
        match constructor_description.cstr_tag with
        | Cstr_extension _ ->
            raise None ExtensibleType
              ("We only support extensible types in patterns at the head. Here,\n"
             ^ "the extensible type is in a nested position.")
        | _ ->
            PathName.of_constructor_description constructor_description
            >>= fun x ->
            Monad.List.map of_pattern ps >>= fun patterns ->
            return
              (let patterns = Util.Option.all patterns in
               patterns
               |> Option.map (fun patterns -> Constructor (x, patterns))))
    | Tpat_alias (p, x, _) ->
        of_pattern p >>= fun pattern ->
        Name.of_ident true x >>= fun x ->
        return (pattern |> Option.map (fun pattern -> Alias (pattern, x)))
    | Tpat_constant c ->
        Constant.of_constant c >>= fun constant ->
        return (Some (Constant constant))
    | Tpat_variant (label, p, _) ->
        let* path_name = PathName.constructor_of_variant_with_error label in
        (match p with
        | None -> return (Some [])
        | Some p ->
            of_pattern p >>= fun pattern ->
            return (pattern |> Option.map (fun pattern -> [ pattern ])))
        >>= fun patterns ->
        return
          (patterns
          |> Option.map (fun patterns -> Constructor (path_name, patterns)))
    | Tpat_record (fields, _) ->
        fields
        |> Monad.List.map (fun (_, label_description, p) ->
               PathName.of_label_description label_description >>= fun x ->
               of_pattern p >>= fun pattern ->
               return (pattern |> Option.map (fun pattern -> (x, pattern))))
        >>= fun fields ->
        return
          (Util.Option.all fields |> Option.map (fun fields -> Record fields))
    | Tpat_array ps ->
        Monad.List.map of_pattern ps >>= fun patterns ->
        raise
          (Util.Option.all patterns
          |> Option.map (fun patterns -> Tuple patterns))
          NotSupported "Patterns on array are not supported"
    | Tpat_or (p1, p2, _) ->
        of_pattern p1 >>= fun pattern1 ->
        of_pattern p2 >>= fun pattern2 ->
        return
          (Option.bind pattern1 (fun pattern1 ->
               pattern2 |> Option.map (fun pattern2 -> Or (pattern1, pattern2))))
    | Tpat_lazy p ->
        of_pattern p >>= fun pattern ->
        raise pattern NotSupported "Lazy patterns are not supported"
    | Tpat_value p -> of_pattern (p :> value general_pattern)
    | Tpat_exception _ ->
        raise None SideEffect "We do not support exception patterns")

let rec is_extensible_pattern_or_any : type kind. kind general_pattern -> bool =
 fun p ->
  match p.pat_desc with
  | Tpat_construct (_, constructor_description, _, _) -> (
      match constructor_description.cstr_tag with
      | Cstr_extension _ -> true
      | _ -> false)
  | Tpat_any -> true
  | Tpat_value pat ->
      is_extensible_pattern_or_any (pat :> value general_pattern)
  | _ -> false

let rec are_extensible_patterns_or_any :
    type kind. bool -> kind general_pattern list -> bool =
 fun need_at_least_one_extensible_pattern ps ->
  match ps with
  | [] -> not need_at_least_one_extensible_pattern
  | p :: ps ->
      is_extensible_pattern_or_any p && are_extensible_patterns_or_any false ps

let rec of_extensible_pattern :
    type k. k general_pattern -> (string * t * Type.t) option Monad.t =
 fun p ->
  let error =
    raise
      (Some ("unexpected_kind_of_pattern", Any, Type.Tuple []))
      Unexpected
      "Unexpected kind of pattern (expected extensible type or an any pattern)"
  in
  match p.pat_desc with
  | Tpat_construct (_, constructor_description, ps, _) -> (
      match constructor_description.cstr_tag with
      | Cstr_extension (path, _) ->
          let* typs =
            ps
            |> Monad.List.map (fun p ->
                   Type.of_type_expr_without_free_vars p.pat_type)
          in
          let* ps = Monad.List.filter_map of_pattern ps in
          return (Some (Path.last path, Tuple ps, Type.Tuple typs))
      | _ -> error)
  | Tpat_any -> return None
  | Tpat_value pat -> of_extensible_pattern (pat :> value general_pattern)
  | _ -> error

(** Get the free variables appearing in a pattern. *)
let rec get_free_vars (p : t) : Name.Set.t =
  let get_free_vars_of_list (ps : t list) : Name.Set.t =
    List.fold_left Name.Set.union Name.Set.empty (List.map get_free_vars ps)
  in
  match p with
  | Any -> Name.Set.empty
  | Constant _ -> Name.Set.empty
  | Variable x -> Name.Set.singleton x
  | Tuple es -> get_free_vars_of_list es
  | Constructor (_, es) -> get_free_vars_of_list es
  | Alias (e, _) -> get_free_vars e
  | Record entries -> get_free_vars_of_list (List.map snd entries)
  | Or (e1, e2) -> get_free_vars_of_list [ e1; e2 ]

let rec has_or_patterns (p : t) : bool =
  match p with
  | Any -> false
  | Constant _ -> false
  | Variable _ -> false
  | Tuple ps -> List.exists has_or_patterns ps
  | Constructor (_, ps) -> List.exists has_or_patterns ps
  | Alias (p, _) -> has_or_patterns p
  | Record fields -> fields |> List.map snd |> List.exists has_or_patterns
  | Or _ -> true

let rec flatten_or (p : t) : t list =
  match p with Or (p1, p2) -> flatten_or p1 @ flatten_or p2 | _ -> [ p ]

(** Pretty-print a pattern to Coq (inside parenthesis if the [paren] flag is set). *)
let rec to_coq (paren : bool) (p : t) : SmartPrint.t =
  match p with
  | Any -> !^"_"
  | Constant c -> Constant.to_coq c
  | Variable x -> Name.to_coq x
  | Tuple ps -> (
      match ps with
      | [] -> !^"tt"
      | [ p ] -> to_coq paren p
      | _ :: _ :: _ ->
          parens @@ nest
          @@ separate (!^"," ^^ space) (List.map (to_coq false) ps))
  | Constructor (x, ps) ->
      if ps = [] then if PathName.is_tt x then !^"_" else PathName.to_coq x
      else
        Pp.parens paren @@ nest
        @@ separate space (PathName.to_coq x :: List.map (to_coq true) ps)
  | Alias (p, x) -> (
      match p with
      | Any -> to_coq paren (Variable x)
      | _ -> Pp.parens paren @@ nest (to_coq true p ^^ !^"as" ^^ Name.to_coq x))
  | Record fields ->
      !^"{|" ^^ nest_all
      @@ separate (!^";" ^^ space)
           (fields
           |> List.map (fun (x, p) ->
                  nest (PathName.to_coq x ^^ !^":=" ^^ to_coq false p)))
      ^^ !^"|}"
  | Or _ ->
      let ps = flatten_or p in
      parens
      @@ group
           (separate (space ^^ !^"|" ^^ space) (ps |> List.map (to_coq false)))
