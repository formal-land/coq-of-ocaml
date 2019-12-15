module M = struct
  let n = 12
end

module N = struct
  let n = true
  let x = n
  open M
  let y = n
end

let b = N.n
open N
let b' = N.n
