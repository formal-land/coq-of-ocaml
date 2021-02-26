type ex = ..

type ex += Empty

type ex += Int of int

type ex += String of string * bool

type ex += Re of {v : string; n : int}

let v0 = Empty

let v1 = Int 12

let v2 = String ("hi", true)

let v3 = Re { v = "message"; n = 10 }

exception Foo of string

exception Bar of { message : string }

let match_ex x : int =
  match x with
  | Empty -> 0
  | Int n -> n
  | String (m, b) -> if b then String.length m else 0
  | Re { v ; n } -> n + String.length v
  | _ -> -1
