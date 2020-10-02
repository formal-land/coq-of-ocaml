module type Sig = sig
  type t

  val v : t
end

type single = C of string foo

and 'a foo = 'a * int * (module Sig with type t = 'a)
