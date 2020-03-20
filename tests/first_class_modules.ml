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

module type IncludedFoo = sig
  type bar
  val foo : bar
end

module type Triple = sig
  type a
  type b
  type c
  val va : a
  val vb : b
  val vc : c
  include IncludedFoo
end

let tripe : (module Triple) =
  (module struct
    type a = int
    type b = bool
    type c = string
    let va = 0
    let vb = false
    let vc = ""
    type bar = int
    let foo = 12
  end)

module type UsingTriple = sig
  type elt'
  module T : Triple
  module OPS' : S.SET
  module OPS'' : S.SET with type elt = elt' and type t = string list
  type 'a table = 'a list
end

let set_update
  : type a. a -> bool -> a set -> a set
  = fun v b (module Box) ->
  (module struct
    type elt = a
    let elt_ty = Box.elt_ty
    module OPS = Box.OPS
    let boxed =
      if b
      then Box.OPS.add v Box.boxed
      else Box.OPS.remove v Box.boxed
    let size =
      let mem = Box.OPS.mem v Box.boxed in
      if mem
      then if b then Box.size else Box.size - 1
      else if b then Box.size + 1 else Box.size
  end)

let set_mem
  : type elt. elt -> elt set -> bool
  = fun v (module Box) ->
    Box.OPS.mem v Box.boxed

let set_fold
  : type elt acc. (elt -> acc -> acc) -> elt set -> acc -> acc
  = fun f (module Box) ->
    Box.OPS.fold f Box.boxed

let set_nested
  : type elt. elt set -> elt set
  = fun (module Box) ->
  (module struct
    let result : elt set =
      (module struct
        type nonrec elt = elt
        let elt_ty = Box.elt_ty
        module OPS = Box.OPS
        let boxed = Box.boxed
        let size = Box.size
      end)
    type nonrec elt = elt
    let elt_ty = Box.elt_ty
    module OPS = Box.OPS
    let boxed = Box.boxed
    let size =
      let (module Result) = result in
      Result.size
  end)

module type MAP = sig
  type key
  type +'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val mem : key -> 'a t -> bool
end
