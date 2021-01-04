(** Some documentation *)
module type Source = sig
  type t
  val x : t
  val id : 'a -> 'a
end

module type Target = sig
  type t
  val y : t
end

module M : Source = struct
  type t = int
  let x = 12
  let id x = x
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

module WithM = struct
  include M
  let z = 0
end

module WithSum = struct
  include F (M)
  let z = 0
end

module GenFun () : Target = struct
  type t = int
  let y = 23
end

module AppliedGenFun : Target = GenFun ()
