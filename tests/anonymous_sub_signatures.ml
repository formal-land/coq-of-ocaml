module type T_bytes = sig
  type t

  val to_bytes : t -> bytes

  val of_bytes_exn : bytes -> t
end

module type T_encoding = sig
  type t

  val encoding : t list
end

module type T_encoding_bytes = sig
  include T_bytes

  include T_encoding with type t := t
end

module type WithBar = sig
  val bar : string
end

module type Validator = sig
  module Ciphertext : sig
    include T_encoding

    val get_memo_size : t -> int
  end

  module Commitment : sig
    val v : string

    include T_encoding_bytes

    val valid_position : int64 -> bool

    module Foo : WithBar
  end

  module CV : T_encoding

  type com = Commitment.t
end

module F (V : Validator) : WithBar = struct
  type foo = V.com
  let bar = V.Commitment.Foo.bar
end
