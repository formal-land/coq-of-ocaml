(** Global identifiers with a module path, used to reference a definition for example. *)
open Asttypes
open SmartPrint

module Path' = Path

module Path = struct
  type t = Name.t list
end

type t = {
  depth : int;
  path : Path.t;
  base : Name.t}

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)

(* Convert an identifier from OCaml to its Coq's equivalent. *)
let convert (path : Path.t) (base : Name.t) : Path.t * Name.t =
  match (path, base) with
  | ([], "()") -> ([], "tt")
  | ([], "int") -> ([], "Z")
  | ([], "char") -> ([], "ascii")
  | ([], "::") -> ([], "cons")
  | (["Pervasives"], x) ->
    (match base with
    | "=" -> ([], "equiv_decb")
    | "<>" -> ([], "nequiv_decb")
    | "<" -> (["Z"], "ltb")
    | "not" -> ([], "negb")
    | "&&" -> ([], "andb")
    | "&" -> failwith "\"&\" is deprecated. Use \"&&\" instead."
    | "||" -> ([], "orb")
    | "or" -> failwith "\"or\" is deprecated. Use \"||\" instead."
    | "|>" -> ([], "reverse_apply")
    | "@@" -> ([], "apply")
    | "~-" -> (["Z"], "opp")
    | "~+" -> ([], "")
    | "succ" -> (["Z"], "succ")
    | "pred" -> (["Z"], "pred")
    | "+" -> (["Z"], "add")
    | "-" -> (["Z"], "sub")
    | "*" -> (["Z"], "mul")
    | "/" -> (["Z"], "div")
    | "mod" -> (["Z"], "modulo")
    | "abs" -> (["Z"], "abs")
    | "land" -> (["Z"], "land")
    | "lor" -> (["Z"], "lor")
    | "lxor" -> (["Z"], "lxor")
    | "lnot" -> failwith "\"lnot\" not handled."
    | "asr" -> failwith "\"asr\" not handled."
    | "lsl" -> (["Z"], "shiftl")
    | "lsr" -> (["Z"], "shiftr")
    | "^" -> ([], "append")
    | "int_of_char" -> ([], "int_of_char")
    | "char_of_int" -> ([], "char_of_int")
    | "ignore" -> ([], "ignore")
    | "string_of_bool" -> failwith "string_of_bool not handled."
    | "bool_of_string" -> failwith "bool_of_string not handled."
    | "string_of_int" -> failwith "string_of_int not handled."
    | "int_of_string" -> failwith "int_of_string not handled."
    | "fst" -> ([], "fst")
    | "snd" -> ([], "snd")
    | "@" -> ([], "app")
    | "invalid_arg" -> ([], "invalid_arg")
    | "failwith" -> ([], "failwith")
    | "print_char" -> ([], "print_char")
    | "print_string" -> ([], "print_string")
    | "print_int" -> ([], "print_int")
    | "print_endline" -> ([], "print_endline")
    | "print_newline" -> ([], "print_newline")
    | "prerr_char" -> ([], "prerr_char")
    | "prerr_string" -> ([], "prerr_string")
    | "prerr_int" -> ([], "prerr_int")
    | "prerr_endline" -> ([], "prerr_endline")
    | "prerr_newline" -> ([], "prerr_newline")
    | "read_line" -> ([], "read_line")
    | "read_int" -> ([], "read_int")
    | _ -> (path, base))
  | _ -> (path, base)

(** Pretty-print a global name. *)
let pp (x : t) : SmartPrint.t =
  single_quotes @@ (separate (!^ ".")
    (List.map (fun s -> !^ s) (x.path @ [x.base])) ^-^ !^ "/" ^-^ OCaml.int x.depth)

(** Lift a local name to a global name. *)
let of_name (depth : int) (path : Path.t) (base : Name.t) : t =
  let (path, base) = convert path base in
  { depth = depth; path = path; base = base }

(** Import an OCaml [Longident.t]. *)
let of_longident (depth : int) (longident : Longident.t) : t =
  match List.rev (Longident.flatten longident) with
  | [] -> failwith "Expected a non empty list."
  | x :: xs -> of_name depth xs x

(** Import an OCaml location. *)
let of_loc (depth : int) (loc : Longident.t loc) : t = 
  of_longident depth loc.txt

(** Import an OCaml [Path.t]. *)
let of_path (depth : int) (p : Path'.t) : t =
  let rec aux p : Path.t * Name.t =
    match p with
    | Path'.Pident x -> ([], Name.of_ident x)
    | Path'.Pdot (p, s, _) ->
      let (path, base) = aux p in
      (base :: path, s)
    | Path'.Papply _ -> failwith "application of paths not handled" in
  let (path, base) = aux p in
  of_name depth (List.rev path) base

(** Pretty-print a global name to Coq. *)
let to_coq (x : t) : SmartPrint.t =
  separate (!^ ".") (List.map Name.to_coq (x.path @ [x.base]))

module Env = struct
  module Map =
    Map.Make (struct type t = Path.t * Name.t let compare = compare end)

  type 'a t = 'a Map.t list

  (*let pp (pp_v : 'a -> SmartPrint.t) (env : 'a t) : SmartPrint.t =
    List.map Map.bindings env |>
    List.concat |>
    OCaml.list (fun (x, v) ->
      nest (pp x ^^ !^ "=>" ^^ pp_v v))*)

  let empty : 'a t = [Map.empty]

  let add (path : Path.t) (base : Name.t) (v : 'a) (env : 'a t) : 'a t =
    match env with
    | map :: env -> Map.add (path, base) v map :: env
    | [] -> failwith "The environment must be a non-empty list."

  let add_name (x : Name.t) (v : 'a) (env : 'a t) : 'a t =
    add [] x v env

  let reference (path : Path.t) (base : Name.t) (env : 'a t) : t' =
    let rec depth env =
      match env with
      | map :: env -> if Map.mem (path, base) map then 0 else 1 + depth env
      | [] -> failwith (base ^ " not found.") in
    { depth = depth env; path = path; base = base }

  let rec find (x : t') (env : 'a t) : 'a =
    let map =
      try List.nth env x.depth with
      | Failure "nth" -> raise Not_found in
    Map.find (x.path, x.base) map

  let mem (x : t') (env : 'a t) : bool =
    try let _ = find x env in true with
    | Not_found -> false

  let fresh (prefix : string) (v : 'a) (env : 'a t) : Name.t * 'a t =
    let prefix_n s n =
      if n = 0 then
        Name.of_string s
      else
        Name.of_string @@ Printf.sprintf "%s_%d" s n in
    let rec first_n (n : int) : int =
      if mem (of_name 0 [] @@ prefix_n prefix n) env then
        first_n (n + 1)
      else
        n in
    let x = prefix_n prefix (first_n 0) in
    (x, add_name x v env)

  let open_module (env : 'a t) : 'a t =
    Map.empty :: env

  let close_module (env : 'a t) (lift : 'a -> Name.t -> 'a) (name : Name.t)
    : 'a t =
    match env with
    | map1 :: map2 :: env ->
      Map.fold (fun (path, base) v map2 ->
        Map.add (name :: path, base) (lift v name) map2)
        map1 map2
        :: env
    | _ -> failwith "At least one module should be opened."
end