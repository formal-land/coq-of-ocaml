module type T = sig
  type t
  val to_string : t -> string
end

module M : T with type t = int = struct
  type t = int
  let to_string = string_of_int
end
[@@coq_plain_module]

let int_to_string : int -> string = M.to_string
