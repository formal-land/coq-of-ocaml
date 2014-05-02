(** Module type *)

module type IM = sig
  val n : int
end

module M : IM = struct
  let b = false
  let n = 12
end