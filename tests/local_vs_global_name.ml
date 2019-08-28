module M : sig
  val n : int
end = struct
  let b = false
  let n = 12
end

let n = M.n + 2
