module type COMPARABLE = sig
  type t

  val compare : t -> t -> int
end

module type S = sig
  type t

  val ( = ) : t -> t -> bool

  val ( <> ) : t -> t -> bool

  val ( < ) : t -> t -> bool

  val ( <= ) : t -> t -> bool

  val ( >= ) : t -> t -> bool

  val ( > ) : t -> t -> bool

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val max : t -> t -> t

  val min : t -> t -> t
end

module Make (P : COMPARABLE) : (S with type t = P.t)

module Char : S with type t = char

module Abstract : S

module Lift (P : COMPARABLE) : COMPARABLE
