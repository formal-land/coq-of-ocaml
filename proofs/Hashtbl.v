Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.
Require CoqOfOCaml.Seq.

(* this might be useful: http://gallium.inria.fr/~fpottier/publis/fpottier-hashtable.pdf*)
Parameter t: Set -> Set -> Set. 

Parameter create : forall {a b : Set}, bool -> int -> t a b.

Parameter clear : forall {a b : Set}, t a b -> unit.

Parameter reset : forall {a b : Set}, t a b -> unit.

Parameter copy : forall {a b : Set}, t a b -> t a b.

Parameter add : forall {a b : Set}, t a b -> a -> b -> unit.

Parameter find : forall {a b : Set}, t a b -> a -> b.

Parameter find_opt : forall {a b : Set}, t a b -> a -> option b .

Parameter find_all : forall {a b : Set}, t a b -> a -> list b.

Parameter mem : forall {a b : Set}, t a b -> a -> bool.

Parameter remove : forall {a b : Set}, t a b -> a -> unit.

Parameter replace : forall {a b : Set}, t a b -> a -> b -> unit.

Parameter iter : forall {a b : Set}, (a -> b -> unit) -> t a b -> unit.

Parameter filter_map_inplace : forall {a b : Set}, (a -> b -> option b) -> t a b -> unit.

Parameter fold : forall {a b c: Set}, (a -> b -> c -> c) -> t a b -> c -> c.

Parameter length : forall {a b : Set}, t a b -> int.

Parameter randomize : unit -> unit.

Parameter is_randomized : unit -> bool.

Parameter rebuild : forall {a b : Set}, bool -> t a b -> t a b.

(* OCaml:
type statistics = {
  num_bindings : int;
  num_buckets : int;
  max_bucket_length : int;
  bucket_histogram : int array;
*)
(* Parameter stats : t a b -> statistics *)
(** Hash tables and Sequences **)
Parameter to_seq : forall {a b : Set}, t a b -> Seq.t (a * b).

Parameter to_seq_keys : forall {a b : Set}, t a b -> Seq.t  a.

Parameter to_seq_Parameterues : forall {a b : Set},  t a b -> Seq.t b.

Parameter add_seq : forall {a b : Set}, t a b -> Seq.t (a * b) -> unit.

Parameter replace_seq : forall {a b : Set}, t a b -> Seq.t (a * b) -> unit.

Parameter of_seq : forall {a b : Set}, Seq.t (a * b) -> t a b.

(** Functorial interface **)
(*
module type HashedType = sig .. end
module type S = sig .. end
module Make: 
  functor (H : HashedType) -> S  with type key = H.t
module type SeededHashedType = sig .. end
module type SeededS = sig .. end
module MakeSeeded:
  functor (H : SeededHashedType) -> SeededS  with type key = H.t
*)
(** The polymorphic hash functions **)
Parameter hash : forall {a : Set}, a -> int.

Parameter seeded_hash : forall {a : Set}, int -> a -> int.

Parameter hash_param : forall {a : Set}, int -> int -> a -> int.

Parameter seeded_hash_param : forall {a : Set}, int -> int -> int -> a -> int.
