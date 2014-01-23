Require Export ZArith.
Require Export Ascii.
Require Export String.
Require Export List.
Require Export Program.Basics.
Require Export Classes.SetoidDec.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition reverse_apply {A B : Type} (x : A) (f : A -> B) : B :=
  f x.

Definition int_of_char (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Definition char_of_int (n : Z) : ascii :=
  ascii_of_nat (Z.to_nat n).

Definition ignore {A : Type} (_ : A) : unit :=
  tt.

(** The concatenation of lists with an implicit parameter. *)
Definition app {A : Type} (l1 l2 : list A) : list A :=
  app l1 l2.

Module Effect.
  Record t := new {
    S : Type;
    E : Type }.
  
  Definition unit : t := {|
    S := unit;
    E := Empty_set |}.
  
  Definition add (e1 e2 : t) : t := {|
    S := S e1 * S e2;
    E := E e1 + E e2 |}.
  
  Fixpoint of_list (es : list t) : t :=
    match es with
    | [] => unit
    | e :: es => add e (of_list es)
    end.
  
  Fixpoint sub (es : list t) (bs : list bool) : list t :=
    match (es, bs) with
    | ([], _) => []
    | (e :: es, b :: bs) =>
      if b then
        e :: sub es bs
      else
        sub es bs
    | (_ :: _, []) => es
    end.
  
  Fixpoint filter (es : list t) (bs : list bool)
    (s : S (of_list es)) {struct es}
    : S (of_list (sub es bs)).
    destruct es as [|e es]; destruct bs as [|b bs]; try exact s.
    destruct b; simpl in *.
    - exact (fst s, filter es bs (snd s)).
    - exact (filter es bs (snd s)).
  Defined.
  
  Fixpoint expand_exception (es : list t) (bs : list bool)
    (err : E (of_list (sub es bs))) {struct es}
    : E (of_list es).
    destruct es as [|e es]; destruct bs as [|b bs]; try exact err.
    destruct b; simpl in *.
    - exact (match err with
      | inl err => inl err
      | inr err => inr (expand_exception es bs err)
      end).
    - exact (inr (expand_exception es bs err)).
  Defined.
  
  Fixpoint expand_state (es : list t) (bs : list bool)
    (s1 : S (of_list (sub es bs))) (s2 : S (of_list es)) {struct es}
    : S (of_list es).
    destruct es as [|e es]; destruct bs as [|b bs]; try exact s1.
    destruct b; simpl in *.
    - exact (fst s1, expand_state es bs (snd s1) (snd s2)).
    - exact (fst s2, expand_state es bs s1 (snd s2)).
  Defined.
End Effect.

Definition M (es : list Effect.t) (A : Type) : Type :=
  let e := Effect.of_list es in
  Effect.S e -> (A + Effect.E e) * Effect.S e.

Definition ret {es : list Effect.t} {A : Type} (x : A) : M es A :=
  fun s => (inl x, s).

Definition bind {es : list Effect.t} {A B : Type}
  (x : M es A) (f : A -> M es B) : M es B :=
  fun s =>
    let (x, s) := x s in
    match x with
    | inl x => f x s
    | inr e => (inr e, s)
    end.

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Definition lift (es : list Effect.t) (bs : list bool) {A : Type}
  (x : M (Effect.sub es bs) A) : M es A :=
  fun s =>
    let (r, s') := x (Effect.filter es bs s) in
    let s := Effect.expand_state es bs s' s in
    match r with
    | inl x => (inl x, s)
    | inr err => (inr (Effect.expand_exception es bs err), s)
    end.

Definition Invalid_argument := Effect.new unit string.

Definition Failure := Effect.new unit string.

Definition IO := Effect.new (list string * list string) Empty_set.

Definition invalid_arg {A : Type} (message : string)
  : M [Invalid_argument] A :=
  fun s => (inr (inl message), s).

Definition failwith {A : Type} (message : string)
  : M [Failure] A :=
  fun s => (inr (inl message), s).

Definition print_string (message : string) : M [IO] unit :=
  fun s =>
    match s with
    | ((stream_i, stream_o), _) =>
      (inl tt, ((stream_i, message :: stream_o), tt))
    end.