module SizedString = struct
  type t = {
    name : string;
    size : int }
end

let r = { SizedString.name = "gre"; size = 3 }
let r' = { SizedString.name = "haha"; size = 4 }

let s = r.SizedString.size + r'.SizedString.size

let f = function
  | { SizedString.size = 3 } -> true
  | _ -> false

let b = f r
let b' = f r'

module Point = struct
  type t = {
    x : int;
    y : int;
    z : int }

  let p = { x = 5; y = -3; z = 1 }

  let b = match p with
    | { x = 5; z = 1 } -> true
    | _ -> false
end

type ('first, 'second) poly = {
  first : 'first;
  second : 'second }

let p = { first = 12; second = false }

module ConstructorWithRecords = struct
  type t =
    | Foo of { name : string; size : int }
    | Bar of loc

  and 'a gadt =
    | Ex : { x : 'a } -> 'a gadt

  and loc = { x : int; y : int }

  let l = { x = 12; y = 23 }

  let l_with = { l with x = 41 }

  let foo = Foo { name = "foo"; size = 12 }

  let f (x : t) =
    match x with
    | Foo { size } -> size
    | Bar { y } -> y
end
