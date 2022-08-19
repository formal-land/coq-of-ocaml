Require Import Libraries.
Require Import Basics.
Require Import Program.Program.

Require Import Seq.

Definition t (A : Set) : Set := array A.

Parameter length :  forall {a : Set}, array a -> int.

Parameter get :  forall {a : Set}, array a -> int -> a.

Parameter set :  forall {a : Set}, array a -> int -> a -> unit.

Parameter make :  forall {a : Set}, int -> a -> array a.

Parameter create :  forall {a : Set}, int -> a -> array a.

Parameter create_float :  forall {a : Set}, int -> array float.

Parameter make_float :  forall {a : Set}, int -> array float.

Parameter init :  forall {a : Set}, int -> (int -> a) -> array a.

Parameter make_matrix :  forall {a : Set}, int -> int -> a -> array (array a).

Parameter create_matrix :  forall {a : Set}, int -> int -> a -> array (array a).

Parameter append :  forall {a : Set}, array a -> array a -> array a.

Parameter concat :  forall {a : Set}, list (array a) -> array a.

Parameter sub :  forall {a : Set}, array a -> int -> int -> array a.

Parameter copy :  forall {a : Set}, array a -> array a.

Parameter fill :  forall {a : Set}, array a -> int -> int -> a -> unit.

Parameter blit :  forall {a : Set}, array a -> int -> array a -> int -> int -> unit.

Parameter to_list :  forall {a : Set}, array a -> list a.

Parameter of_list :  forall {a : Set}, list a -> array a.

(** Iterators **)
Parameter iter :  forall {a : Set}, (a -> unit) -> array a -> unit.

Parameter iteri :  forall {a : Set}, (int -> a -> unit) -> array a -> unit.

Parameter map :  forall {a b : Set}, (a -> b) -> array a -> array b.

Parameter mapi :  forall {a b : Set}, (int -> a -> b) -> array a -> array b.

Parameter fold_left :  forall {a b : Set}, (a -> b -> a) -> a -> array b -> a.

Parameter fold_left_map :  forall {a b c : Set}, (a -> b -> a * c) -> a -> array b -> a * array c.

Parameter fold_right :  forall {a b : Set}, (b -> a -> a) -> array b -> a -> a.

(** Iterators on two arrays **)
Parameter iter2 :  forall {a b : Set}, (a -> b -> unit) -> array a -> array b -> unit.

Parameter map2 :  forall {a b c : Set}, (a -> b -> c) -> array a -> array b -> array c.

(** Array scanning **)
Parameter for_all :  forall {a : Set}, (a -> bool) -> array a -> bool.

Parameter _exists :  forall {a : Set}, (a -> bool) -> array a -> bool.

Parameter for_all2 :  forall {a b : Set}, (a -> b -> bool) -> array a -> array b -> bool.

Parameter _exists2 :  forall {a b : Set}, (a -> b -> bool) -> array a -> array b -> bool.

Parameter mem :  forall {a : Set}, a -> array a -> bool.

Parameter memq :  forall {a : Set}, a -> array a -> bool.

Parameter find_opt :  forall {a : Set}, (a -> bool) -> array a -> option a.

Parameter find_map :  forall {a b : Set}, (a -> option b) -> array a -> option b.

(** Arrays of pairs **)
Parameter split :  forall {a b : Set}, array (a * b) -> array a * array b.

Parameter combine :  forall {a b : Set}, array a -> array b -> array (a * b).

(** Sorting **)
Parameter sort :  forall {a : Set}, (a -> a -> int) -> array a -> unit.

Parameter stable_sort :  forall {a : Set}, (a -> a -> int) -> array a -> unit.

Parameter fast_sort :  forall {a : Set}, (a -> a -> int) -> array a -> unit.

(** Arrays and Sequences **)
Parameter to_seq :  forall {a : Set}, array a -> Seq.t a.

Parameter to_seqi :  forall {a : Set}, array a -> Seq.t (int * a).

Parameter of_seq :  forall {a : Set}, Seq.t a -> array a.
