Require Import Libraries.

Local Open Scope Z_scope.
Import ListNotations.
Set Implicit Arguments.

Definition sum_assoc_left (A B C : Type) (x : A + (B + C)) : (A + B) + C :=
  match x with
  | inl x => inl (inl x)
  | inr (inl x) => inl (inr x)
  | inr (inr x) => inr x
  end.

Module Effect.
  Record t := make {
    S : Type;
    E : Type }.
  
  Definition nil : t := {|
    S := unit;
    E := Empty_set |}.
  
  Definition add (e1 e2 : t) : t := {|
    S := S e1 * S e2;
    E := E e1 + E e2 |}.
  
  Fixpoint of_list (es : list t) : t :=
    match es with
    | [] => nil
    | e :: es => add e (of_list es)
    end.
  
  Definition state (es : list t) : Type :=
    S (of_list es).
  
  Definition error (es : list t) : Type :=
    E (of_list es).
  
  Module Ebs.
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
    
    Fixpoint filter_state (ebs : list (t * bool)) (s : state (domain ebs))
      {struct ebs} : state (sub ebs).
      destruct ebs as [|[e b] ebs].
      - exact s.
      - destruct b; simpl in *.
        + exact (fst s, filter_state ebs (snd s)).
        + exact (filter_state ebs (snd s)).
    Defined.
    
    Fixpoint expand_exception (ebs : list (t * bool))
      (err : error (sub ebs)) {struct ebs}
      : error (domain ebs).
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
      (s1 : state (sub ebs)) (s2 : state (domain ebs))
      {struct ebs} : state (domain ebs).
      destruct ebs as [|[e b] ebs].
      - exact s1.
      - destruct b; simpl in *.
        + exact (fst s1, expand_state ebs (snd s1) (snd s2)).
        + exact (fst s2, expand_state ebs s1 (snd s2)).
    Defined.
  End Ebs.
End Effect.

Module Raw.
  Definition M (es : list Effect.t) (A : Type) : Type :=
    Effect.state es -> (A + Effect.error es) * Effect.state es.

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

  Definition lift {A : Type} (es : list Effect.t) (bs : string)
    (x : M _ A) : M _ A :=
    let aux (ebs : list (Effect.t * bool)) (x : M (Effect.Ebs.sub ebs) A)
      : M (Effect.Ebs.domain ebs) A :=
      fun s =>
        let (r, s') := x (Effect.Ebs.filter_state ebs s) in
        let s := Effect.Ebs.expand_state ebs s' s in
        match r with
        | inl x => (inl x, s)
        | inr err => (inr (Effect.Ebs.expand_exception ebs err), s)
        end in
    let fix bool_list (s : string) : list bool :=
      match s with
      | EmptyString => []
      | String "0" s => false :: bool_list s
      | String _ s => true :: bool_list s
      end in
    aux (List.combine es (bool_list bs)) x.
End Raw.

Definition M (es : list Effect.t) (A : Type) : Type :=
  match es with
  | [] => A
  | _ => Effect.state es -> (A + Effect.error es) * Effect.state es
  end.

Definition of_raw {es : list Effect.t} {A : Type} : Raw.M es A -> M es A :=
  match es with
  | [] => fun x =>
    match x tt with
    | (inl x, _) => x
    | (inr err, _) => match err with end
    end
  | _ => fun x => x
  end.

Definition to_raw {es : list Effect.t} {A : Type} : M es A -> Raw.M es A :=
  match es with
  | [] => fun x => fun tt => (inl x, tt)
  | _ => fun x => x
  end.

Definition ret {es : list Effect.t} {A : Type} (x : A) : M es A :=
  of_raw (Raw.ret x).

Definition bind {es : list Effect.t} {A B : Type}
  (x : M es A) (f : A -> M es B) : M es B :=
  of_raw (Raw.bind (to_raw x) (fun x => to_raw (f x))).

Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
  (at level 200, X ident, A at level 100, B at level 200).

Definition lift {A : Type} (es : list Effect.t) (bs : string)
  (x : M _ A) : M _ A :=
  of_raw (Raw.lift es bs (to_raw x)).

Module Exception.
  Fixpoint remove_nth (es : list Effect.t) (n : nat) : list Effect.t :=
    match es with
    | [] => []
    | e :: es =>
      match n with
      | O => es
      | S n => e :: remove_nth es n
      end
    end.

  Definition nth_is_stateless (es : list Effect.t) (n : nat) : Type :=
    match List.nth_error es n with
    | Some e => Effect.S e
    | None => unit
    end.
  
  Fixpoint input (es : list Effect.t) (n : nat) (tt' : nth_is_stateless es n)
    (s : Effect.state (remove_nth es n)) {struct es} : Effect.state es.
    destruct es as [|e es].
    - exact s.
    - destruct n as [|n].
      + exact (tt', s).
      + refine (fst s, input es n tt' (snd s)).
  Defined.
  
  Fixpoint output (es : list Effect.t) (n : nat) (s : Effect.state es)
    {struct es} : Effect.state (remove_nth es n).
    destruct es as [|e es].
    - exact s.
    - destruct n as [|n].
      + exact (snd s).
      + exact (fst s, output _ _ (snd s)).
  Defined.
  
  Fixpoint error (es : list Effect.t) (n : nat) (err : Effect.error es)
    {struct es}
    : Effect.E (nth n es Effect.nil) + Effect.error (remove_nth es n).
    destruct es as [|e es].
    - destruct err.
    - destruct n as [|n].
      + exact err.
      + refine (
          match err with
          | inl err => inr (inl err)
          | inr err =>
            match error _ _ err with
            | inl err => inl err
            | inr err => inr (inr err)
            end
          end).
  Defined.
  
  Definition run {A : Type} {es : list Effect.t} (n : nat)
    (x : M es A) (tt' : nth_is_stateless es n)
    : M (remove_nth es n) (A + Effect.E (List.nth n es Effect.nil)) :=
    of_raw (fun s =>
      let (r, s) := (to_raw x) (input _ _ tt' s) in
      (match r with
      | inl x => inl (inl x)
      | inr err => sum_assoc_left (inr (error _ _ err))
      end, output _ _ s)).
End Exception.

Module Run.
  Fixpoint remove_nth (es : list Effect.t) (n : nat) : list Effect.t :=
    match es with
    | [] => []
    | e :: es =>
      match n with
      | O => es
      | S n => e :: remove_nth es n
      end
    end.
  
  Fixpoint input (es : list Effect.t) (n : nat)
    (s : Effect.S (List.nth n es Effect.nil))
    (ss : Effect.state (remove_nth es n)) {struct es} : Effect.state es.
    destruct es as [|e es].
    - exact ss.
    - destruct n as [|n].
      + exact (s, ss).
      + refine (fst ss, input es n s (snd ss)).
  Defined.
  
  Fixpoint output (es : list Effect.t) (n : nat) (ss : Effect.state es)
    {struct es}
    : Effect.S (List.nth n es Effect.nil) * Effect.state (remove_nth es n).
    destruct es as [|e es].
    - destruct n; exact (tt, ss).
    - destruct n as [|n].
      + exact (fst ss, snd ss).
      + exact (
        let (s, ss') := output _ _ (snd ss) in
        (s, (fst ss, ss'))).
  Defined.
  
  Fixpoint error (es : list Effect.t) (n : nat) (err : Effect.error es)
    {struct es}
    : Effect.E (nth n es Effect.nil) + Effect.error (remove_nth es n).
    destruct es as [|e es].
    - destruct err.
    - destruct n as [|n].
      + exact err.
      + refine (
          match err with
          | inl err => inr (inl err)
          | inr err =>
            match error _ _ err with
            | inl err => inl err
            | inr err => inr (inr err)
            end
          end).
  Defined.
  
  Definition run {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    : let S := Effect.S (List.nth n es Effect.nil) in
      let E := Effect.E (List.nth n es Effect.nil) in
      S -> M (remove_nth es n) ((A + E) * S) :=
    fun s => of_raw (fun ss =>
      let (r, ss) := (to_raw x) (input _ _ s ss) in
      let (s, ss) := output es n ss in
      (match r with
      | inl x => inl (inl x, s)
      | inr err =>
        match error es n err with
        | inl e => inl (inr e, s)
        | inr ee => inr ee
        end
      end, ss)).
  
  (** Expected value for [tt']: [tt]. *)
  Definition exception {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    (tt' : Effect.S (List.nth n es Effect.nil))
    : M (remove_nth es n) (A + Effect.E (List.nth n es Effect.nil)) :=
    let! x := run n x tt' in
    ret (fst x).
  
  (** Expected value for [error_is_empty]: [fun err => match err with end]. *)
  Definition reader {A : Type} {es : list Effect.t} (n : nat) (x : M es A)
    (error_is_empty : Effect.E (List.nth n es Effect.nil) -> False)
    : Effect.S (List.nth n es Effect.nil) -> M (remove_nth es n) A :=
    fun s =>
      let! x := run n x s in
      match fst x with
      | inl x => ret x
      | inr err => False_rect _ (error_is_empty err)
      end.
End Run.

(** A stream which may be finite. *)
Module FiniteStream.
  CoInductive t (A : Type) : Type :=
  | nil : t A
  | cons : A -> t A -> t A.
End FiniteStream.

Definition IO := Effect.make (FiniteStream.t string * list string) Empty_set.

Definition Counter := Effect.make nat Empty_set.

Definition NonTermination := Effect.make unit unit.

Definition read_counter (_ : unit) : M [Counter] nat :=
  fun s => (inl (fst s), s).

Definition not_terminated {A : Type} (_ : unit) : M [NonTermination] A :=
  fun s => (inr (inl tt), s).