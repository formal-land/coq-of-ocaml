module type S = sig
  type t
  val v : t
end

module M_infer = struct
  type t = int
  let v = 12
end

module M_definition : S with type t = int = struct
  type t = int
  let v = 12
end

module M_abstract : S = struct
  type t = int
  let v = 12
end

module F_definition (M1 : S) (M2 : S)
  : S with type t = M1.t * M2.t * string = struct
  type t = M1.t * M2.t * string
  let v = (M1.v, M2.v, "foo")
end

module F_abstract (M1 : S) (M2 : S) : S = struct
  type t = M1.t * M2.t * string
  let v = (M1.v, M2.v, "foo")
end