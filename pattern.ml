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
  let open_paren () = if paren then Format.fprintf f "(" in
  let close_paren () = if paren then Format.fprintf f ")" in
  match p with
  | Any -> Format.fprintf f "_"
  | Variable x -> Name.pp f x
  | Tuple ps ->
    Format.fprintf f "(";
    pp f false (List.hd ps);
    List.iter (fun p ->
      Format.fprintf f ",@ ";
      pp f false p)
      (List.tl ps);
    Format.fprintf f ")"
  | Constructor (path, ps) ->
    if ps = [] then
      PathName.pp f path
    else (
      open_paren ();
      PathName.pp f path;
      List.iter (fun p ->
        Format.fprintf f "@ ";
        pp f true p) ps;
      close_paren ())
