---
id: ocaml-core
title: OCaml core
---

`coq-of-ocaml` translates the functional core of [OCaml](https://ocaml.org/) to the corresponding [Coq](https://coq.inria.fr/) constructs. It adds type annotations for each definition. We present how this translation work.

## Functions
The OCaml functions are translated to standard Coq functions. For example, the definition of the composition function in OCaml:
```ocaml
let compose g f x =
  g (f x)
```
produces in Coq:
```coq
Definition compose {A B C : Set} (g : A -> B) (f : C -> A) (x : C) : B :=
  g (f x).
```
The polymorphic variables `A`, `B` and `C` are written explicitly as there are no polymorphic type inference in Coq (it is unclear if type variables should be in `Set`, `Type` or `Prop` for example). These polymorphic variables are set implicit with `{...}` so that they are inferred when doing function application:
```ocaml
let incr n = n + 1

let plus_two = compose incr incr
```
is translated to:
```coq
Definition incr (n : Z) : Z := Z.add n 1.

Definition plus_two : Z -> Z := compose incr incr.
```
> All the generated types are in `Set`. You may need to use the [`-impredicative-set`](https://github.com/coq/coq/wiki/Impredicative-Set) option of Coq to allow complex cases of polymorphism. An alternative is to replace all the generated occurrences of `Set` by `Type`. However, this may expose you to universe inconsistencies in proofs.

## Pattern-matching
The pattern-matching is handled in Coq. The main difference is that constructors are curryfied:
```ocaml
type 'a sequence =
  | Empty
  | Cons of 'a * 'a sequence

let rec sum s =
  match s with
  | Empty -> 0
  | Cons (n, s') -> n + sum s'
```
generates:
```coq
Inductive sequence (a : Set) : Set :=
| Empty : sequence a
| Cons : a -> sequence a -> sequence a.

Arguments Empty {_}.
Arguments Cons {_}.

Fixpoint sum (s : sequence Z) : Z :=
  match s with
  | Empty => 0
  | Cons n s' => Z.add n (sum s')
  end.
```

The `when` clauses on patterns are encoded with a tuple of matches:
```ocaml
let rec sum s =
  match s with
  | Empty -> 0
  | Cons (n, _) when n < 0 -> sum s'
  | Cons (n, s') -> n + sum s'
```
generates:
```coq
Fixpoint sum (s : sequence Z) : Z :=
  match
    (s,
      match s with
      | Cons n s' => OCaml.Stdlib.lt n 0
      | _ => false
      end) with
  | (Empty, _) => 0
  | (Cons n s', true) => sum s'
  | (Cons n s', _) => Z.add n (sum s')
  end.
```

## Records
Coq is more restrictive on the naming of record fields than OCaml. Two different records cannot share a common field name.
```ocaml
type answer = {
  code : int;
  message : string }
```
generates:
```coq
Module answer.
  Record record := {
    code : Z;
    message : string }.
  Definition with_code (r : record) code : record :=
    {| code := code; message := message r |}.
  Definition with_message (r : record) message : record :=
    {| code := code r; message := message |}.
End answer.
Definition answer := answer.record.
```
Records in Coq are automatically namespaced into a module of the same name. This prevents name collisions between record fields. As Coq has no builtin constructs for substitution in records, `coq-of-ocaml` generates a `with_` function for each of the fields.

To read into the record, the generated code prefixes all the fields by the record's name:
```ocaml
let get_answer_message answer =
  answer.message
```
generates:
```coq
Definition get_answer_message (answer : answer) : string :=
  answer.(answer.message).
```
Patterns on records are also translated:
```ocaml
let get_answer_code = function
  { code } -> code
```
generates:
```coq
Definition get_answer_code (function_parameter : answer) : Z :=
  let '{| answer.code := code |} := function_parameter in
  code.
```

## Recursive definitions
In Coq all functions must be proven terminating. We disable the termination checks for now by using the [TypingFlags plugin](https://github.com/SimonBoulier/TypingFlags) (this feature should be included in the upcoming Coq 8.11 release). At the start of every generated files, `coq-of-ocaml` unset the termination flag:
```coq
Require Import TypingFlags.Loader.
Unset Guard Checking.
```
Unsetting the termination also remove the strict positivity checks for the definition of inductive types. We will probably add an option to re-activate the termination check when possible.

## Monadic notations
The OCaml language provides a way to define [monadic operators](https://caml.inria.fr/pub/docs/manual-ocaml/bindingops.html) so that we can define programs such as:
```ocaml
let return (x : 'a) : 'a option =
  Some x

let (let*) (x : 'a option) (f : 'a -> 'b option) : 'b option =
  match x with
  | Some x -> f x
  | None -> None

let get_head l =
  match l with
  | [] -> None
  | x :: _ -> Some x

let sum_first_elements l1 l2 =
  let* x1 = get_head l1 in
  let* (x2, x3) = get_head l2 in
  return (x1 + x2 + x3)
```
We translate the program using similar let-notations in Coq. We require the user to manually insert these notations. For example, here `coq-of-ocaml` generates:
```coq
Definition _return {a : Set} (x : a) : option a := Some x.

Definition op_letstar {a b : Set} (x : option a) (f : a -> option b)
  : option b :=
  match x with
  | Some x => f x
  | None => None
  end.

Definition get_head {A : Set} (l : list A) : option A :=
  match l with
  | [] => None
  | cons x _ => Some x
  end.

Definition sum_first_elements (l1 : list int) (l2 : list (int * int))
  : option int :=
  let* x1 := get_head l1 in
  let* '(x2, x3) := get_head l2 in
  _return (Z.add (Z.add x1 x2) x3).
```
By adding the following notations in the generated code:
```coq
Notation "'let*' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x ident, X at level 100, Y at level 200).

Notation "'let*' ' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).
```
the function `get_head` compiles. Note that `coq-of-ocaml` does not generate these notations, and you have to add them by hand.
