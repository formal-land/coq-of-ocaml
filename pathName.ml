type t = {
  path : Name.t list;
  base : Name.t}

let of_name (x : Name.t) : t =
  { path = []; base = x }

let of_path (p : Path.t) : t =
  let rec aux p =
    match p with
    | Path.Pident i -> { path = []; base = Name.of_ident i }
    | Path.Pdot (p, s, _) ->
      let p = aux p in
      { path = p.base :: p.path; base = s }
    | Path.Papply _ -> failwith "application of paths not handled" in
  let p = aux p in
  let p = { path = List.rev p.path; base = p.base } in
  (* We convert identifiers from OCaml to their Coq's equivalents *)
  match p with
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "int" } -> { path = []; base = "Z" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = ["Pervasives"]; base = x } -> (match x with
    | "=" -> { path = []; base = "equiv_decb" }
    | "<>" -> { path = []; base = "nequiv_decb" }
    | "not" -> { path = []; base = "negb" }
    | "&&" -> { path = []; base = "andb" }
    | "&" -> failwith "\"&\" is deprecated. Use \"&&\" instead."
    | "||" -> { path = []; base = "orb" }
    | "or" -> failwith "\"or\" is deprecated. Use \"||\" instead."
    | "|>" -> { path = []; base = "(flip apply)" } (* TODO: test it using OCaml 4.1 *)
    | "@@" -> { path = []; base = "apply" } (* TODO: test it using OCaml 4.1 *)
    | "~-" -> { path = ["Z"]; base = "opp" }
    | "~+" -> { path = []; base = "" }
    | "succ" -> { path = ["Z"]; base = "succ" }
    | "pred" -> { path = ["Z"]; base = "pred" }
    | "+" -> { path = ["Z"]; base = "add" }
    | "-" -> { path = ["Z"]; base = "sub" }
    | "*" -> { path = ["Z"]; base = "mul" }
    | "/" -> { path = ["Z"]; base = "div" }
    | "mod" -> { path = ["Z"]; base = "modulo" }
    | "abs" -> { path = ["Z"]; base = "abs" }
    | "land" -> { path = ["Z"]; base = "land" }
    | "lor" -> { path = ["Z"]; base = "lor" }
    | "lxor" -> { path = ["Z"]; base = "lxor" }
    | "lnot" -> failwith "\"lnot\" not handled."
    | "asr" -> failwith "\"asr\" not handled."
    | "lsl" -> { path = ["Z"]; base = "shiftl" }
    | "lsr" -> { path = ["Z"]; base = "shiftr" }
    | "^" -> { path = []; base = "append" }
    | "int_of_char" -> { path = []; base = "(compose Z.of_nat nat_of_ascii)" }
    | "char_of_int" -> { path = []; base = "(compose ascii_of_nat Z.to_nat)" }
    | "ignore" -> { path = []; base = "(fun _ => tt)" }
    | "string_of_bool" -> failwith "string_of_bool not handled."
    | "bool_of_string" -> failwith "bool_of_string not handled."
    | "string_of_int" -> failwith "string_of_int not handled."
    | "int_of_string" -> failwith "int_of_string not handled."
    | "fst" -> { path = []; base = "fst" }
    | "snd" -> { path = []; base = "snd" }
    | "@" -> { path = []; base = "app" }
    | _ -> p)
  | _ -> p

let pp (f : Format.formatter) (i : t) : unit =
  List.iter (fun x -> Name.pp f x; Format.fprintf f ".") i.path;
  Name.pp f i.base
