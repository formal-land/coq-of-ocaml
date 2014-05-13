(** Module type *)

module type IM1 = sig
  val n : int
  val f : 'a -> 'a * 'b

  type 'a t1 =
    | C1 of int
    | C2 of 'a * bool

  type t2 = {
    f1 : int;
    f2 : bool }

  type 'a t3 = int * 'a

  type t4

  type ('a, 'b) t5
end

module type IM2 = sig
  type t
  val m : int
  val b : t
end

module M2 : IM2 = struct
  let null = (0, false)
  type t = bool
  let m = 12
  let b = false
end