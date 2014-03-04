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
  
  Fixpoint domain (ebs : list (t * bool)) : list t :=
    match ebs with
    | [] => []
    | (e, _) :: ebs => e :: domain ebs
    end.
  
  Fixpoint sub (ebs : list (t * bool)) : list t :=
    match ebs with
    | [] => []
    | (_, false) :: ebs => sub ebs
    | (e, true) :: ebs => e :: sub ebs
    end.
  
  Fixpoint filter (ebs : list (t * bool))
    (s : S (of_list (domain ebs))) {struct ebs}
    : S (of_list (sub ebs)).
    destruct ebs as [|[e b] ebs].
    - exact s.
    - destruct b; simpl in *.
      + exact (fst s, filter ebs (snd s)).
      + exact (filter ebs (snd s)).
  Defined.
  
  Fixpoint expand_exception (ebs : list (t * bool))
    (err : E (of_list (sub ebs))) {struct ebs}
    : E (of_list (domain ebs)).
    destruct ebs as [|[e b] ebs].
    - exact err.
    - destruct b; simpl in *.
      + exact (match err with
        | inl err => inl err
        | inr err => inr (expand_exception ebs err)
        end).
      + exact (inr (expand_exception ebs err)).
  Defined.
  
  Fixpoint expand_state (ebs : list (t * bool))
    (s1 : S (of_list (sub ebs))) (s2 : S (of_list (domain ebs)))
    {struct ebs} : S (of_list (domain ebs)).
    destruct ebs as [|[e b] ebs].
    - exact s1.
    - destruct b; simpl in *.
      + exact (fst s1, expand_state ebs (snd s1) (snd s2)).
      + exact (fst s2, expand_state ebs s1 (snd s2)).
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

Definition lift {A : Type} (es : list Effect.t) (bs : string)
  (x : M _ A) : M _ A :=
  let aux (ebs : list (Effect.t * bool)) (x : M (Effect.sub ebs) A)
    : M (Effect.domain ebs) A :=
    fun s =>
      let (r, s') := x (Effect.filter ebs s) in
      let s := Effect.expand_state ebs s' s in
      match r with
      | inl x => (inl x, s)
      | inr err => (inr (Effect.expand_exception ebs err), s)
      end in
  let fix bool_list (s : string) : list bool :=
    match s with
    | EmptyString => []
    | String "0" s => false :: bool_list s
    | String _ s => true :: bool_list s
    end in
  aux (List.combine es (bool_list bs)) x.

Definition Invalid_argument := Effect.new unit string.

Definition Failure := Effect.new unit string.

Definition IO := Effect.new (list string * list string) Empty_set.

Definition Counter := Effect.new nat Empty_set.

Definition NonTermination := Effect.new unit unit.

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

Definition read_counter (_ : unit) : M [Counter] nat :=
  fun s => (inl (fst s), s).

Definition not_terminated {A : Type} (_ : unit) : M [NonTermination] A :=
  fun s => (inr (inl tt), s).