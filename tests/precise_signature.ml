module type Sig1 = sig
  type t

  val f : t -> t -> t * t
end
[@@coq_precise_signature]

module type Sig2 = sig
  type t

  val f : t -> t list
end
[@@coq_precise_signature]

module M1 : Sig1 = struct
  type t = int

  let f (n : t) m = (n, m)
end

module M2 : Sig2 = struct
  type t = int

  let f (n : t) = []
end
