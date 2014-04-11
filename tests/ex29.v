Require Import CoqOfOCaml.

Local Open Scope Z_scope.
Import ListNotations.

Fixpoint odd_length {A : Type} (l : list A) : bool :=
  match l with
  | [] => false
  | cons _ l => negb (even_length l)
  end

with even_length {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | cons _ l => negb (odd_length l)
  end.

Fixpoint odd_length_with_print {A : Type} (l : list A) : M [ IO ] bool :=
  match l with
  | [] =>
    let! _ := OCaml.Pervasives.print_endline "false" % string in
    ret false
  | cons _ l =>
    let! x := even_length_with_print l in
    ret (negb x)
  end

with even_length_with_print {A : Type} (l : list A) : M [ IO ] bool :=
  match l with
  | [] => ret true
  | cons _ l =>
    let! x := odd_length_with_print l in
    ret (negb x)
  end.

Fixpoint odd_length_free_rec {A : Type} (counter : nat) (l : list A)
  : M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret false
    | cons _ l =>
      let! x := (even_length_free_rec counter) l in
      ret (negb x)
    end
  end

with even_length_free_rec {A : Type} (counter : nat) (l : list A)
  : M [ NonTermination ] bool :=
  match counter with
  | O => not_terminated tt
  | S counter =>
    match l with
    | [] => ret true
    | cons _ l =>
      let! x := (odd_length_free_rec counter) l in
      ret (negb x)
    end
  end.

Definition odd_length_free {A : Type} (l : list A)
  : M [ Counter; NonTermination ] bool :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (odd_length_free_rec x l).

Definition even_length_free {A : Type} (l : list A)
  : M [ Counter; NonTermination ] bool :=
  let! x := lift [_;_] "10" (read_counter tt) in
  lift [_;_] "01" (even_length_free_rec x l).
