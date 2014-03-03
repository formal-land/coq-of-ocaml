open SmartPrint

type t = int option

let unknown : t = None

let pp (l : t) : SmartPrint.t =
  match l with
  | None -> !^ "?"
  | Some n -> OCaml.int n