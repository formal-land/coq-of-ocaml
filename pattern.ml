open Typedtree

type t =
  | Any
  | Variable of Name.t
  | Tuple of t list
  | Constructor of PathName.t * t list

let rec of_pattern (p : pattern) : t =
  match p.pat_desc with
  | Tpat_any -> Any
  | Tpat_var (x, _) -> Variable (Name.of_ident x)
  | Tpat_tuple ps -> Tuple (List.map of_pattern ps)
  | Tpat_construct (path, _, _, ps, _) -> Constructor (PathName.of_path path, List.map of_pattern ps)
  | _ -> failwith "unhandled pattern"

let rec pp (f : Format.formatter) (paren : bool) (p : t) : unit =
  match p with
  | Any -> Format.fprintf f "_"
  | Variable x -> Name.pp f x
  | Tuple ps ->
    Format.fprintf f "(";
    Pp.sep_by ps (fun _ -> Format.fprintf f ",@ ") (fun p -> pp f false p);
    Format.fprintf f ")"
  | Constructor (path, ps) ->
    if ps = [] then
      PathName.pp f path
    else (
      Pp.open_paren f paren;
      PathName.pp f path;
      Format.fprintf f "@ ";
      Pp.sep_by ps (fun _ -> Format.fprintf f "@ ") (fun p -> pp f true p);
      Pp.close_paren f paren)
