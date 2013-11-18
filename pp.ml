(** Pretty-printing helpers. *)
open Format

(** Open a parenthesis according to a flag. *)
let open_paren (f : formatter) (b : bool) : unit =
  if b then fprintf f "("

(** Close a parenthesis according to a flag. *)
let close_paren (f : formatter) (b : bool) : unit =
  if b then fprintf f ")"

(** Apply [pp] to each element of the list [l] and call [sep] between each element. *)
let sep_by (l : 'a list) (sep : unit -> unit) (pp : 'a -> unit) : unit =
  match l with
  | [] -> ()
  | x :: xs ->
    pp x;
    List.iter (fun x -> sep (); pp x) xs
