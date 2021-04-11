---
id: module-system
title: Module system
---

To handle the module system of OCaml, the compiler `coq-of-ocaml` generates either plain Coq modules or dependent records. It never generates Coq functors or module types. You can use `coq-of-ocaml` to translate modules, module types, functors and first-class modules.

## General mechanism
### Example
The following code:
```ocaml
module MyModuleForNamespacing = struct
  let foo x = x + 1
  let bar = 12
end

module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
end

module InstanceToUseInFunctors = struct
  type t = string
  let compare = String.compare
end
```
is translated to:
```coq
Module MyModuleForNamespacing.
  Definition foo (x : Z) : Z := Z.add x 1.
  
  Definition bar : Z := 12.
End MyModuleForNamespacing.

Module COMPARABLE.
  Record signature {t : Set} := {
    t := t;
    compare : t -> t -> Z;
  }.
  Arguments signature : clear implicits.
End COMPARABLE.

Definition InstanceToUseInFunctors :=
  let t := string in
  let compare := Stdlib.String.compare in
  existT (fun _ => _) tt
    {|
      COMPARABLE.compare := compare
    |}.
```
We use a plain module for `MyModuleForNamespacing` as we think it will not be used in functors or first-class modules. We translate the module type `COMPARABLE` to a record parametrized by `t` as this type is abstract. The `InstanceToUseInFunctors` is translated to a dependent record of type `COMPARABLE.signature` as it may by used as a parameter for a functor for example. We will see how we determine that a module should translates to a record.

### Finding names
The heuristic is to represent a module by a dependent record if and only if it has a named signature. The name of the signature is then the name of the record type. Each signature is translated to a record type.

The OCaml modules are structurally typed while the Coq records are nominally typed. Thus a large part of the conversion effort is dedicated to the naming of signatures. A signature is named by exploring the environment to find a similar signature definition with its name. Two signatures are deemed similar if they share the same list of names of values and sub-modules at top-level. We do not check for type names or values as they could be removed or changed by the use of type substitutions (operators `with type t = ...` and `with type t := ...`). We only check top-level names for efficiency reasons, and because exploring sub-modules resulted in errors in some cases.

We generate an error message when multiple names are found for a signature. For example with:
```ocaml
module type S1 = sig
  val v : string
end

module type S2 = sig
  val v : int
end

module M = struct
  let v = "hi"
end
```
the module `M` could have the signatures `S1` or `S2` as we only look at the value names, so we output the error:
```text
   7 | end
   8 | 
>  9 | module M = struct
  10 |   let v = "hi"
  11 | end
  12 | 


It is unclear which name has this signature. At least two similar
signatures found, namely:
S2, S1

We were looking for a module signature name for the following shape:
[ v ]
(a shape is a list of names of values and sub-modules)

We use the concept of shape to find the name of a signature for Coq.
```
To discriminate between two similar signatures, you can add a dummy tag field. With:
```ocaml
module type S1 = sig
  val this_is_S1 : unit
  val v : string
end

module type S2 = sig
  val this_is_S2 : unit
  val v : int
end

module M = struct
  let this_is_S1 = ()
  let v = "hi"
end
```
`coq-of-ocaml` generates without errors:
```coq
Module S1.
  Record signature := {
    this_is_S1 : unit;
    v : string;
  }.
End S1.

Module S2.
  Record signature := {
    this_is_S2 : unit;
    v : Z;
  }.
End S2.

Definition M :=
  let this_is_S1 := tt in
  let v := "hi" in
  existT (fun _ => _) tt
    {|
      S1.this_is_S1 := this_is_S1;
      S1.v := v
    |}.
```

If no signatures are found, the module `M` is translated to a plain Coq module:
```ocaml
module type S = sig
  val v : string
end

module M = struct
  let not_v = "hi"
end
```
generates:
```coq
Module S.
  Record signature := {
    v : string;
  }.
End S.

Module M.
  Definition not_v : string := "hi".
End M.
```

### Bundled vs unbundled
In OCaml modules may have some abstract types. In Coq we represent abstract types as type parameters for the records of the signatures. For module values, we instantiate known abstract types and use existential types for unknown abstract types. We always use a single existential `{... & ...}` on the tuple of unknown types. If all types are known, we still use an existential on the empty tuple for uniformity.

We say that:
* signatures are always unbundled (with universal types);
* module are always bundled (with existential types).

## Signatures
Signatures can contain a mix of:
* abstract types (constant or polymorphic);
* type definitions as synonyms;
* values;
* sub-modules.

A complex example is the following:
```ocaml
module type SubS = sig
  type t
  val v : t
  type size
  val n : size
end

module type S = sig
  type 'a t
  type int_t = int t
  val numbers : int_t
  module Sub : SubS with type t = int_t
  val n : Sub.size
end
```
which gets translated to:
```coq
Module SubS.
  Record signature {t size : Set} := {
    t := t;
    v : t;
    size := size;
    n : size;
  }.
  Arguments signature : clear implicits.
End SubS.

Module S.
  Record signature {t : Set -> Set} {Sub_size : Set} := {
    t := t;
    int_t := t Z;
    numbers : int_t;
    Sub : SubS.signature int_t Sub_size;
    n : Sub.(SubS.size);
  }.
  Arguments signature : clear implicits.
End S.
```

The signature `SubS` has two abstract types `t` and `size`. We define two synonym record fields `t := t` and `size := size` for uniform access.

The signature `S` is parametrized by its abstract type `t` and the abstract type `Sub_size` of its sub-module `Sub`. The abstract type `t` is polymorphic and of type `Set -> Set`. The type synonym `int_t` is defined as a synonym record field. The sub-module `Sub` is a field of the record `S.signature` and of type the record `SubS.signature`. Its type parameter `t` is instantiated by `int_t`. Note that sub-module values appear as *unbundled* records. This is the only case where module values are unbundled. We made this choice because the abstract types of the sub-module `Sub` may be instantiated later as in:
```ocaml
S with type Sub.size = int
```
Finally, a signature field such as `n` can refer to a type defined in the sub-module `Sub`.

## Modules
The modules with a named signature are represented as bundled dependent records. The abstract types are generally known at the moment of the definition, but may still be hidden by casting. For example, the following code:
```ocaml
module type Source = sig
  type t
  val x : t
end

module M_NoCast = struct
  type t = int
  let x = 12
end

module M_WithCast : Source = struct
  type t = int
  let x = 12
end
```
will generate:
```coq
Module Source.
  Record signature {t : Set} := {
    t := t;
    x : t;
  }.
  Arguments signature : clear implicits.
End Source.

Definition M_NoCast :=
  let t := Z in
  let x := 12 in
  existT (fun _ => _) tt
    {|
      Source.x := x
    |}.

Definition M_WithCast :=
  let t := Z in
  let x := 12 in
  existT _ _
    {|
      Source.x := x
    |}.
```
The module `M_NoCast` has no existential variables while the module `M_WithCast` has one due to the cast to the `Source` signature. This is visible in the use a `_` to ask Coq to infer the value of this type, in place of a `tt` to represent the absence of existential variables.

### Existential tuples
In the presence of several existential variables we use tuples of types with primitive projections. Primitive projections help Coq to infer missing values in generated terms, so that we do not need to annotate too much module expressions. These tuples are a variant of the tuples of the standard library. We use the following notations:
```coq
[T1 * T2 * ... Tn] (* the type of a tuple *)
[v1, v2, ..., vn]  (* the value of tuple *)
```
A tuple of *n* values is encoded as *n-1* nested tuples of two values.

### Projections
As modules are always bundled (unless in the case of sub-modules in signatures), we introduce a notation for the Coq projection `projT2`:
```coq
(|bundled_record|)
```
Thus projections from modules encoded as a record:
```ocaml
let x = M_WithCast.x
```
typically have this shape in Coq:
```coq
Definition x : (|M_WithCast|).(Source.t) := (|M_WithCast|).(Source.x).
```
We did not add a notation for doing both the projection and the field access, as this would mess up with the inference for implicit variables in polymorphic fields.

## Include
Includes, either in signatures or modules, are generally inlined. For example, with signatures:
```ocaml
module type COMPARABLE = sig
  type t
  val compare : t -> t -> int
end

module type S = sig
  include COMPARABLE
  val ( = ) : t -> t -> bool
  val ( <> ) : t -> t -> bool
  val ( < ) : t -> t -> bool
  val ( <= ) : t -> t -> bool
  val ( >= ) : t -> t -> bool
  val ( > ) : t -> t -> bool
  val equal : t -> t -> bool
  val max : t -> t -> t
  val min : t -> t -> t
end
```
generates:
```coq
Module COMPARABLE.
  Record signature {t : Set} := {
    t := t;
    compare : t -> t -> Z;
  }.
  Arguments signature : clear implicits.
End COMPARABLE.

Module S.
  Record signature {t : Set} := {
    t := t;
    compare : t -> t -> Z;
    op_eq : t -> t -> bool;
    op_ltgt : t -> t -> bool;
    op_lt : t -> t -> bool;
    op_lteq : t -> t -> bool;
    op_gteq : t -> t -> bool;
    op_gt : t -> t -> bool;
    equal : t -> t -> bool;
    max : t -> t -> t;
    min : t -> t -> t;
  }.
  Arguments signature : clear implicits.
End S.
```
Due to duplications, `coq-of-ocaml` may generate Coq terms which are larger than the corresponding OCaml code. If you want to keep a generated Coq without duplications, we recommend you to use sub-modules rather than includes.

## Functors
We represent functors as functions over bounded records. Here is the example of a functor declaration:
```ocaml
module Make (P : COMPARABLE) : (S with type t = P.t)
```
generating:
```coq
Parameter Make :
  forall (P : {t : _ & COMPARABLE.signature t}),
    {_ : unit & S.signature (|P|).(COMPARABLE.t)}.
```
We see that the return type of `Make` is a dependent type depending on the value of the field `COMPARABLE.t` of `P`. A functor may also return another functor.

Here is an example of functor definition and application:
```ocaml
module type Source = sig
  type t
  val x : t
end

module type Target = sig
  type t
  val y : t
end

module F (X : Source) : Target with type t = X.t = struct
  type t = X.t
  let y = X.x
end

module M : Source = struct
  type t = int
  let x = 12
end

module N = F (M)
```
generating:
```coq
Module Source.
  Record signature {t : Set} := {
    t := t;
    x : t;
  }.
  Arguments signature : clear implicits.
End Source.

Module Target.
  Record signature {t : Set} := {
    t := t;
    y : t;
  }.
  Arguments signature : clear implicits.
End Target.

Definition F :=
  fun (X : {t : _ & Source.signature t}) =>
    (let t := (|X|).(Source.t) in
    let y := (|X|).(Source.x) in
    existT (fun _ => _) tt
      {|
        Target.y := y
      |} : {_ : unit & Target.signature (|X|).(Source.t)}).

Definition M :=
  let t := Z in
  let x := 12 in
  existT _ _
    {|
      Source.x := x
    |}.

Definition N :=
  F
    (existT _ _
      {|
        Source.x := (|M|).(Source.x)
      |}).
```

Applications of functors are represented by standard function applications. We cast the module parameter to make sure he has the correct record type. We cast records by re-creating them with the right field names.

## First-class modules
First-class modules are modules which appear as values in OCaml. The encoding to dependent records provides a perfect way to represent them in Coq. Here is an example from the Tezos source code:
```ocaml
module type Boxed_set = sig
  type elt
  val elt_ty : elt comparable_ty
  module OPS : S.SET with type elt = elt
  val boxed : OPS.t
  val size : int
end

type 'elt set = (module Boxed_set with type elt = 'elt)

let set_mem
  : type elt. elt -> elt set -> bool
  = fun v (module Box) ->
    Box.OPS.mem v Box.boxed
```
generates:
```coq
Module Boxed_set.
  Record signature {elt OPS_t : Set} := {
    elt := elt;
    elt_ty : comparable_ty elt;
    OPS : S.SET.signature elt OPS_t;
    boxed : OPS.(S.SET.t);
    size : Z;
  }.
  Arguments signature : clear implicits.
End Boxed_set.

Definition set (elt : Set) := {OPS_t : _ & Boxed_set.signature elt OPS_t}.

Definition set_mem {elt : Set} (v : elt) (Box : set elt) : bool :=
  (|Box|).(Boxed_set.OPS).(S.SET.mem) v (|Box|).(Boxed_set.boxed).
```
Many things are happening here, but the main thing to know is that we do not need to represent the OCaml lifts "module to value" or "value to module" since dependent records are already values in Coq.
