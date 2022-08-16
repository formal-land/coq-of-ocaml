Require Import CoqOfOCaml.Libraries.
Require Import CoqOfOCaml.Settings.
Require Import CoqOfOCaml.Basics.

Reserved Notation "'t".

Inductive node (A : Set) : Set :=
| Nil : node A
| Cons : A -> 't A -> node A

where "'t" := (fun (T : Set) => unit -> node T).

Definition t := 't.

Arguments Nil {_}.
Arguments Cons {_}.

(** Consuming sequences **)
Parameter is_empty : forall {a : Set},  t a -> bool.

Parameter uncons : forall {a : Set},  t a -> option (a * t a) .

Parameter length : forall {a : Set},  t a -> int.

Parameter iter : forall {a : Set},  (a -> unit) -> t a -> unit.

Parameter fold_left : forall {a b : Set},  (a -> b -> a) -> a -> t b -> a.

Parameter iteri : forall {a : Set},  (int -> a -> unit) -> t a -> unit.

Parameter fold_lefti : forall {a b : Set},  (b -> int -> a -> b) -> b -> t a -> b.

Parameter for_all : forall {a : Set},  (a -> bool) -> t a -> bool.

Parameter _exists : forall {a : Set},  (a -> bool) -> t a -> bool.

Parameter find : forall {a : Set},  (a -> bool) -> t a -> option a.

Parameter find_map : forall {a b : Set},  (a -> option b) -> t a -> option b.

Parameter iter2 : forall {a b : Set},  (a -> b -> unit) -> t a -> t b -> unit.

Parameter fold_left2 : forall {a b c : Set},  (a -> b -> c -> a) -> a -> t b -> t c -> a.

Parameter for_all2 : forall {a b : Set},  (a -> b -> bool) -> t a -> t b -> bool.

Parameter _exists2 : forall {a b : Set},  (a -> b -> bool) -> t a -> t b -> bool.

Parameter equal : forall {a b : Set},  (a -> b -> bool) -> t a -> t b -> bool.

Parameter compare : forall {a b : Set},  (a -> b -> int) -> t a -> t b -> int.

(** Constructing sequences **)
Parameter empty : forall {a : Set},  t a.

Parameter _return : forall {a : Set},  a -> t a.

Parameter cons : forall {a : Set},  a -> t a -> t a.

Parameter init : forall {a : Set},  int -> (int -> a) -> t a.

Parameter unfold : forall {a b : Set},  (b -> option (a * b)) -> b -> t a.

Parameter repeat : forall {a : Set},  a -> t a.

Parameter forever : forall {a : Set},  (unit -> a) -> t a.

Parameter cycle : forall {a : Set},  t a -> t a.

Parameter iterate : forall {a : Set},  (a -> a) -> a -> t a.

(** Transforming sequences **)
Parameter map : forall {a b : Set},  (a -> b) -> t a -> t b.

Parameter mapi : forall {a b : Set},  (int -> a -> b) -> t a -> t b.

Parameter filter : forall {a : Set},  (a -> bool) -> t a -> t a.

Parameter filter_map : forall {a b : Set},  (a -> option b) -> t a -> t b.

Parameter scan : forall {a b : Set},  (b -> a -> b) -> b -> t a -> t b.

Parameter take : forall {a : Set},  int -> t a -> t a.

Parameter drop : forall {a : Set},  int -> t a -> t a.

Parameter take_while : forall {a : Set},  (a -> bool) -> t a -> t a.

Parameter drop_while : forall {a : Set},  (a -> bool) -> t a -> t a.

Parameter group : forall {a : Set},  (a -> a -> bool) -> t a -> t (t a).

Parameter memoize : forall {a : Set},  t a -> t a.

(* exception Forced_twice. *)
(* This exception is raised when a sequence returned by Seq.once 
    (or a suffix of it) is queried more than once. *)

Parameter once : forall {a : Set},  t a -> t a.

Parameter transpose : forall {a : Set},  t (t a) -> t (t a).

(** Combining sequences **)
Parameter append : forall {a : Set},  t a -> t a -> t a.

Parameter concat : forall {a : Set},  t (t a) -> t a.

Parameter flat_map : forall {a b : Set},  (a -> t b) -> t a -> t b.

Parameter concat_map : forall {a b : Set},  (a -> t b) -> t a -> t b.

Parameter zip : forall {a b : Set},  t a -> t b -> t (a * b).

Parameter map2 : forall {a b c: Set},  (a -> b -> c) -> t a -> t b -> t c.

Parameter interleave : forall {a : Set},  t a -> t a -> t a.

Parameter sorted_merge : forall {a : Set},  (a -> a -> int) -> t a -> t a -> t a.

Parameter product : forall {a b : Set},  t a -> t b -> t (a * b).

Parameter map_product : forall {a b c : Set},  (a -> b -> c) -> t a -> t b -> t c.

(** Splitting a sequence into two sequences **)
Parameter unzip : forall {a b : Set},  t (a * b) -> t a * t b.

Parameter split : forall {a b : Set},  t (a * b) -> t a * t b.

(*
Parameter partition_map : forall {a b c : Set},  
    (a -> Either.t (b, c)) -> t a -> t b * t c.
*)

Parameter partition : forall {a : Set},  (a -> bool) -> t a -> t a * t a.

(** Converting between sequences and dispensers **)
Parameter of_dispenser : forall {a : Set},  (unit -> option a) -> t a.

Parameter to_dispenser : forall {a : Set},  t a -> unit -> option a.

(** Sequences of integers **)
Parameter ints : forall {a : Set},  int -> t int.
