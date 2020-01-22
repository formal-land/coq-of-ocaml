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

module F (X : Source) : Target with type t = X.t = struct
  type t = X.t
  let y = X.x
end

module FSubst (X : Source) : Target with type t := X.t = struct
  let y = X.x
end

module Sum
  (X : Source with type t = int)
  (Y : Source with type t = int)
  : Target = struct
  type t = int
  let y = X.x + Y.x
end
