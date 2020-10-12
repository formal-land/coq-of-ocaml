module Notations = struct
  let keep_same x = x

  let (+) s1 s2 =
    s1 ^ s2
end

let concat s1 s2 =
  let open Notations in
  keep_same (s1 + s2)
