module type Source = sig
  type t
  val x : t
end

module type Target = sig
  type t
  val y : t
end

module M : Source = struct
  type t = int
  let x = 12
end
