(** Module type *)

module type M = sig
  type t
  val m : int
  module N : sig
    val n : t
    type t
  end
  open N
  val b : t
end

module M : M = struct
  let null = (0, false)
  type t = int
  let m = 12
  let b = false
  module N = struct
    type t = bool
    let n = 14
  end
end