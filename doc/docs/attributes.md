---
id: attributes
title: Attributes
---

We present the attributes which we can use with coq-of-ocaml. See the [attributes documentation](https://caml.inria.fr/pub/docs/manual-ocaml/attributes.html) of OCaml for general information about the attributes mechanism. Note that the OCaml attributes do not change the behavior of a program. There are there to help developer tools.

We prefix all the attributes of coq-of-ocaml by `coq_`. According to the OCaml syntax, depending on the context, you may use a single `@` or a double `@@`.

## coq_axiom
When we cannot import the definition of a value, we can use the `[@coq_axiom]` attribute to transform it to a Coq axiom. For example:
```ocaml
let[@coq_axiom "mutable state"] function_hard_to_translate_to_coq =
  let n = ref 0 in
  fun () ->
    n := !n + 1;
    !n
```
is translated to:
```coq
Definition function_hard_to_translate_to_coq : unit -> Z := axiom.
```
Note that we must give a reason for the use of `[@coq_axiom]` in a string parameter. We define the `axiom` value in the coq-of-ocaml's Coq library. The definition of `axiom` is:
```coq
Axiom axiom : forall {A : Set}, A.
```

## coq_force_gadt
The `[@coq_force_gadt]` attribute forces a type definition to be considered as a GADT during the translation to Coq. In particular, it forces the translation to erase the type parameters. For example:
```ocaml
type 'a standard_list =
  | SNil
  | SCons of 'a * 'a standard_list

type 'a gadt_list =
  | GNil
  | GCons of 'a * 'a gadt_list
[@@coq_force_gadt]
```
generates:
```coq
Inductive standard_list (a : Set) : Set :=
| SNil : standard_list a
| SCons : a -> standard_list a -> standard_list a.

Arguments SNil {_}.
Arguments SCons {_}.

Inductive gadt_list : Set :=
| GNil : gadt_list
| GCons : forall {a : Set}, a -> gadt_list -> gadt_list.
```

One possible reason to force a type to be a GADT is to make sure that all the inductive types in a mutually recursive type definition have the same (zero) arity, as it is expected by Coq.

## coq_implicit
The `[@coq_implicit "(A := ...)"]` attribute adds an arbitrary annotation on an OCaml identifier or constructor. We typically use this attribute to help Coq to infer implicit types where there is an ambiguity:
```ocaml
let forget x = ()

let u = forget []
```
generates the following Coq code:
```coq
Definition forget {A : Set} (x : A) : unit := tt.

Definition u : unit := forget nil.
```
which fails to compile due to the error:
```
> Definition u : unit := forget nil.
>                               ^^^
Error: Cannot infer the implicit parameter A of nil whose type is "Set".
```
Indeed, the type parameter of this empty list does not matter as it is dropped by the `forget` function. We can force it to an arbitrary value like `unit`:
```ocaml
let u = forget ([] [@coq_implicit "(A := unit)"])
```
so that the generated Coq code compiles:
```coq
Definition u : unit := forget (nil (A := unit)).
```

## coq_match_gadt
The `[@coq_match_gadt]` attribute adds type annotations for the pattern variables in a `match`. We force the type annotations to be valid using axioms (dynamic casts). For example:
```ocaml
type 'a int_or_bool =
  | Int : int int_or_bool
  | Bool : bool int_or_bool

let to_int (type a) (kind : a int_or_bool) (x : a) : int =
  match[@coq_match_gadt] (kind, x) with
  | (Int, (x : int)) -> x
  | (Bool, (x : bool)) -> if x then 1 else 0
```
translates to:
```coq
Inductive int_or_bool : Set :=
| Int : int_or_bool
| Bool : int_or_bool.

Definition to_int {a : Set} (kind : int_or_bool) (x : a) : Z :=
  match (kind, x) with
  | (Int, _ as x) =>
    let x := cast Z x in
    x
  | (Bool, _ as x) =>
    let x := cast bool x in
    if x then
      1
    else
      0
  end.
```
The `cast` operator is a dynamic cast defined by:
```coq
Axiom cast : forall {A : Set} (B : Set), A -> B.
```

Note that without the `[@coq_match_gadt]` attribute this would generate:
```coq
Definition to_int {a : Set} (kind : int_or_bool) (x : a) : Z :=
  match (kind, x) with
  | (Int, _ as x) => x
  | (Bool, _ as x) =>
    if x then
      1
    else
      0
  end.
```
which is ill-typed in Coq.

## coq_match_gadt_with_result
The attribute `[@coq_match_gadt_with_result]` is similar to `[@coq_match_gadt]` and also adds a cast for the result of each `match` branch. Here is an example where it is useful:
```ocaml
let incr_if_int (type a) (kind : a int_or_bool) (x : a) : a =
  match[@coq_match_gadt_with_result] (kind, x) with
  | (Int, (x : int)) -> x + 1
  | (Bool, (x : bool)) -> x 
```
generates in Coq:
```coq
Definition incr_if_int {a : Set} (kind : int_or_bool) (x : a) : a :=
  match (kind, x) with
  | (Int, _ as x) =>
    let x := cast Z x in
    cast a (Z.add x 1)
  | (Bool, _ as x) =>
    let x := cast bool x in
    cast a x
  end.
```

## coq_match_with_default
The `[@coq_match_with_default]` adds a default branch for `match` which are syntactically incomplete. For example, when we annotate the following code:
```ocaml
let incr_int (kind_and_value : int int_or_bool * int) : int =
  match[@coq_match_with_default] kind_and_value with
  | (Int, x) -> x + 1
```
we generate the following valid Coq code:
```coq
Definition incr_int (kind_and_value : int_or_bool * Z) : Z :=
  match kind_and_value with
  | (Int, x) => Z.add x 1
  | _ => unreachable_gadt_branch
  end.
```
even if the `match` is syntactically incomplete due to the GADT's constraints. We define `unreachable_gadt_branch` as an axiom by:
```coq
Axiom unreachable_gadt_branch : forall {A : Set}, A.
```

We can combine this attribute with `[@coq_match_gadt]` or `[@coq_match_gadt_with_result]` if needed.

## coq_phantom
When it can, coq-of-ocaml detects phantom types and remove their type annotations. For example, we translate the following OCaml code:
```ocaml
type 'a num = int

type even = Even

let two : even num = 2
```
to:
```coq
Definition num : Set := Z.

Inductive even : Set :=
| Even : even.

Definition two : num := 2.
```
The reason is that phantom types may generate ambiguities during type inference in Coq.

The `[@coq_phantom]` attribute forces coq-of-ocaml to consider a type as phantom. This can be useful for abstract types in `.mli` files, since their definition is not reachable. For example:
```ocaml
type 'a num
```
translates to:
```coq
Parameter num : forall (a : Set), Set.
```
but:
```ocaml
type 'a num
[@@coq_phantom]
```
generates:
```coq
Parameter num : Set.
```

## coq_struct
For recursive definitions, we can force the name of the parameter on which we do structural recursion using the attribute `[@coq_struct "name"]`. This has the same effect as the `{struct name}` keyword in Coq. For example, we translate:
```ocaml
let[@coq_struct "accumulator"] rec length l accumulator =
  match l with
  | [] -> accumulator
  | _ :: l -> length l (accumulator + 1)
```
to:
```coq
Fixpoint length {A : Set} (l : list A) (accumulator : Z) {struct accumulator}
  : Z :=
  match l with
  | [] => accumulator
  | cons _ l => length l (Z.add accumulator 1)
  end.
```
which is invalid in Coq as the decreasing argument is `l`.
