module S = struct
  module type SET = sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val map: (elt -> elt) -> t -> t
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt_opt: t -> elt option
    val max_elt_opt: t -> elt option
    val choose_opt: t -> elt option
    val split: elt -> t -> t * bool * t
    val find_opt: elt -> t -> elt option
    val find_first_opt: (elt -> bool) -> t -> elt option
    val find_last_opt: (elt -> bool) -> t -> elt option
    val of_list: elt list -> t
  end
end

type type_annot = Type_annot of string
type field_annot = Field_annot of string

type ('a, 'b) pair = 'a * 'b

type comb = Comb
type leaf = Leaf

type (_, _) comparable_struct =
  | Int_key : type_annot option -> (int, 'position) comparable_struct
  | String_key : type_annot option -> (string, 'position) comparable_struct
  | Bool_key : type_annot option -> (bool, 'position) comparable_struct
  | Pair_key :
      (('a, leaf) comparable_struct * field_annot option) *
      (('b, 'position) comparable_struct * field_annot option) *
      type_annot option -> (('a, 'b) pair, comb) comparable_struct

type 'a comparable_ty = ('a, comb) comparable_struct

module type Boxed_set = sig
  type elt
  val elt_ty : elt comparable_ty
  module OPS : S.SET with type elt = elt
  val boxed : OPS.t
  val size : int
end

type 'elt set = (module Boxed_set with type elt = 'elt)

module type Triple = sig
  type a
  type b
  type c
end

module type UsingTriple = sig
  type elt'
  module T : Triple
  module OPS' : S.SET
  module OPS'' : S.SET with type elt = elt' and type t = string list
  type 'a table = 'a list
end
