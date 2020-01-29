---
id: ocaml-core
title: OCaml core
---

coq-of-ocaml translates the functional core of [OCaml](https://ocaml.org/) to the corresponding [Coq](https://coq.inria.fr/) constructs. It adds type annotations for each definition. We present how this translation work.

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
Records in Coq are automatically namespaced into a module of the same name. This prevents name collisions between record fields. As Coq has no builtin constructs for substitution in records, coq-of-ocaml generates a `with_` function for each of the fields.

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
In Coq all functions must be proven terminating. We disable the termination checks for now by using the [TypingFlags plugin](https://github.com/SimonBoulier/TypingFlags) (this feature should be included in the upcoming Coq 8.11 release). At the start of every generated files, coq-of-ocaml unset the termination flag:
```coq
Require Import TypingFlags.Loader.
Unset Guard Checking.
```
Unsetting the termination also remove the strict positivity checks for the definition of inductive types. We will probably add an option to re-activate the termination check when possible.
