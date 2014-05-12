(** Functors *)

module type S = sig
  type t

  val x : t
  val f : t -> t
end

module F (M : S) = struct
  let y = M.f M.x
end

module M : S = struct
  type t = int
  let x = 12
  let f x = x + 1
end

module N = F (M)

let n = N.y