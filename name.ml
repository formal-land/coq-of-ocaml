type t = string

let of_ident (i : Ident.t) : t =
  i.Ident.name

let of_pattern (p : Typedtree.pattern) : t =
  match p.Typedtree.pat_desc with
  | Typedtree.Tpat_var (i, _) -> of_ident i
  | _ -> failwith "unhandled pattern"

let pp (f : Format.formatter) (n : t) : unit =
  Format.fprintf f "%s" n

type t' = t
module Set = Set.Make (struct type t = t' let compare = compare end)
