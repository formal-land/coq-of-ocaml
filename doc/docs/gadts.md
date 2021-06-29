---
id: gadts
title: GADTs
---

We provide some support for the [OCaml's GADTs](https://caml.inria.fr/pub/docs/manual-ocaml/manual033.html), which are an advanced form of algebraic data-types. As [Coq](https://coq.inria.fr/) does not have a direct equivalent for the GADTs, we introduce some axioms guided by the user annotations.

For example, the following annotated, but valid, OCaml code:
```ocaml
type 'a int_or_string =
  | Int : int int_or_string
  | String : string int_or_string

let to_string (type a) (kind : a int_or_string) (x : a) : string =
  match[@coq_match_gadt] kind, x with
  | Int, (x : int) -> string_of_int x
  | String, (x : string) -> x
```
will generate the Coq code:
```coq
Reserved Notation "'int_or_string".

Inductive int_or_string_gadt : Set :=
| Int : int_or_string_gadt
| String : int_or_string_gadt

where "'int_or_string" := (fun (_ : Set) => int_or_string_gadt).

Definition int_or_string := 'int_or_string.

Definition to_string {A : Set} (kind : int_or_string A) (x : A) : string :=
  match (kind, x) with
  | (Int, _ as x) =>
    let 'existT _ tt x := obj_magic_exists (fun _ => Z) x in
    obj_magic string (OCaml.Stdlib.string_of_int x)
  | (String, _ as x) =>
    let 'existT _ tt x := obj_magic_exists (fun _ => string) x in
    obj_magic string x
  end.
```
which does type-check. We need to prove that the `obj_magic` axioms are correct if we then want to evaluate the `to_string` function in Coq.

## Existential types
Algebraic data-types with existential types but constant type parameters are a special case of GADTs. We handle existential types automatically and without using axioms, as Coq supports existential types. For example, we translate:
```ocaml
type printable = Printable : 'a * ('a -> string) -> printable

let printable_to_string (x : printable) : string =
  let Printable (value, print) = x in
  print value
```
to:
```coq
Inductive printable : Set :=
| Printable : forall {a : Set}, a -> (a -> string) -> printable.

Definition printable_to_string (x : printable) : string :=
  let 'Printable value print := x in
  let 'existT _ __Printable_'a [value, print] :=
    existT
      (fun __Printable_'a : Set =>
        [__Printable_'a ** (__Printable_'a -> string)]) _ [value, print] in
  print value.
```
The `let 'existT` command names the existential type variables with the same name as in OCaml. Indeed, in OCaml, Merlin would show `$Printable_'a` for the type of `value`. This is not required to type-check this example, but it may be useful to:
* debug;
* validate sub-expression with type annotations using `__Printable_'a`.

## GADTs
We handle the general case of GADTs by erasing the type parameters. Indeed, we did not achieve to use the type parameters so we prefer to remove them to:
* prevent clutter;
* avoid some "strict positivity" errors when defining inductive types annotated by themselves.

Reusing the example of the introduction, we see that for:
```ocaml
type 'a int_or_string =
  | Int : int int_or_string
  | String : string int_or_string
```
we define a second type without type annotations `int_or_string_gadt`:
```coq
Reserved Notation "'int_or_string".

Inductive int_or_string_gadt : Set :=
| Int : int_or_string_gadt
| String : int_or_string_gadt

where "'int_or_string" := (fun (_ : Set) => int_or_string_gadt).

Definition int_or_string := 'int_or_string.
```
but keep the polymorphic `int_or_string` type to preserve type arity. We simply drop the type parameter.
> Dropping type parameters in Coq may incur some issues to infer implicit type variables. We recommend to add type annotations with the OCaml attribute `[@coq_implicits "(A := _)"]` when Coq does not achieve to infer type variables.

To compile the pattern-matching in GADT mode we require an attribute `[@coq_match_gadt]` in OCaml:
```ocaml
let to_string (type a) (kind : a int_or_string) (x : a) : string =
  match[@coq_match_gadt] kind, x with
  | Int, (x : int) -> string_of_int x
  | String, (x : string) -> x
```
This also works with the `function` keyword. For `coq-of-ocaml` to generate valid code, we add the variable `x` in the match. Indeed, the type `a` of `x` is unified during the match, either to `int` or `string`. We also precise this type for each branch with an annotation `(x : int)` to disambiguate from `(x : a)`. In Coq, we introduce two unsafe casts `obj_magic` in each branch:
* one for the variables of the pattern; this cast may also introduce some existential variables;
* one to unify the types of the results of the branches.
```coq
Definition to_string {A : Set} (kind : int_or_string A) (x : A) : string :=
  match (kind, x) with
  | (Int, _ as x) =>
    let 'existT _ tt x := obj_magic_exists (fun _ => Z) x in
    obj_magic string (OCaml.Stdlib.string_of_int x)
  | (String, _ as x) =>
    let 'existT _ tt x := obj_magic_exists (fun _ => string) x in
    obj_magic string x
  end.
```

## Obj_magic
We define two axioms in Coq:
```coq
Axiom obj_magic : forall {A : Set} (B : Set), A -> B.

Axiom obj_magic_exists : forall {As Bs : Type} (T : Bs -> Type),
  As -> {vs : Bs & T vs}.
```
These (unsafe) axioms correspond to arbitrary casts between two types, the second form also introducing some existential variables. To evaluate these axioms when doing proofs on the generated code, we can use:
```coq
Axiom obj_magic_eval : forall {A : Set} {x : A}, obj_magic A x = x.

Axiom obj_magic_exists_eval
  : forall {Es : Type} {T : Es -> Set} {vs : Es} {x : T vs},
  obj_magic_exists T x = existT _ vs x.
```
Applying these evaluation axioms amounts to verifying that the type constraints from OCaml are indeed valid. We need to have the right invariants on our data-types to be able to evaluate these axioms. Indeed, since we remove type annotations from the GADTs, we could construct invalid GADT values in Coq. Values produced as output of imported OCaml functions (not parametrized by GADTs) should always be valid according to the type-checker of OCaml

Here is a proof example to show that our `to_string` function is the identity on the strings:
```coq
Lemma to_string_on_string_is_id (s : string)
  : to_string String s = s.
  unfold to_string.
  rewrite (obj_magic_exists_eval (T := fun _ => _) (vs := tt)).
  rewrite obj_magic_eval.
  reflexivity.
Qed.
```

## Tagged GADTs
Sometimes erasing the type parameters is undesirable because it will drastically change the semantics of your OCaml programs, this can make some properties to be unprovable.
With this in mind we provide a tagging mechanism to achieve this through the flag `[@@coq_tag_gadt]`

For example, we would translate
```ocaml
type 'a term =
  | T_Int : int -> int term
  | T_String : string -> string term
[@@coq_tag_gadt]
```

to: 
```coq
Inductive term : vtag -> Set :=
| T_Int : int -> term int_tag
| T_String : string -> term string_tag
| T_Sum : term int_tag -> term int_tag -> term int_tag.
```

This allows us to directly translate impossible branches over GADTs without the use of the axiom `unreachable_gadt_branch` as follows:
```ocaml
let rec get_int (e : int term) : int =
  match[@coq_tagged_match][@coq_match_with_default] e with
  | T_Int n -> n
  | _ -> .
```
Please notice that we have to indicate that we are pattern matching against a tagged GADT with the flag `coq_tagged_match`.

```coq
Fixpoint get_int (e : term int_tag) : int :=
  match e in term t0 return t0 = int_tag -> int with
  | T_Int n => fun eq0 => ltac:(subst; exact n)
  | _ => ltac:(discriminate)
  end eq_refl.
```

For more details on the mechanisms behind this translation please check [this blog post](https://pedroabreu0.github.io/blog/2020/08/05/OCaml-GADTs-In-Coq)
