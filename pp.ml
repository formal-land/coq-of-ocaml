(** Pretty-printing helpers. *)
open Format

let open_paren (f : formatter) (b : bool) : unit =
  if b then fprintf f "("

let close_paren (f : formatter) (b : bool) : unit =
  if b then fprintf f ")"

let sep_by (l : 'a list) (sep : unit -> unit) (pp : 'a -> unit) : unit =
  match l with
  | [] -> ()
  | x :: xs ->
    pp x;
    List.iter (fun x -> sep (); pp x) xs
