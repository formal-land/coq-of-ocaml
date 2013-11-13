type t = {
  path : Name.t list;
  base : Name.t}

let of_path (p : Path.t) : t =
  let rec aux p =
    match p with
    | Path.Pident i -> { path = []; base = Name.of_ident i }
    | Path.Pdot (p, s, _) ->
      let i = aux p in
      { path = s :: i.path; base = i.base }
    | Path.Papply _ -> failwith "application of paths not handled" in
  let p = aux p in
  (* We convert identifiers from OCaml to their Coq's equivalents *)
  match p with
  | { path = []; base = "()" } -> { path = []; base = "tt" }
  | { path = []; base = "int" } -> { path = []; base = "nat" }
  | { path = []; base = "char" } -> { path = []; base = "ascii" }
  | { path = []; base = "::" } -> { path = []; base = "cons" }
  | { path = ["+"]; base = "Pervasives" } -> { path = []; base = "plus" }
  | _ -> p

let pp (f : Format.formatter) (i : t) : unit =
  List.iter (fun x -> Name.pp f x; Format.fprintf f ".") i.path;
  Name.pp f i.base
