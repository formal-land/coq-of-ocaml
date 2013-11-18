(** Records *)
type t = {
  name : string;
  size : int }

let r = { name = "gre"; size = 3 }
let r' = { name = "haha"; size = 4 }

let s = r.size + r'.size