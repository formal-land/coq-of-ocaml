type t

val foo : t

type ('a, 'b) arg

val x : 'a -> 'b -> ('a, 'b) arg

module M : sig
  type 'a l =
    | Nil
    | Cons of 'a * 'a l

  val b : bool
end
