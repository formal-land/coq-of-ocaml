---
id: module-system
title: Module system
---

To handle the module system of OCaml, the compiler coq-of-ocaml generates either plain Coq modules or dependent records. It never generates Coq functors or module types. You can use coq-of-ocaml to translate modules, module types, functors and first-class modules.

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
coq-of-ocaml generates without errors:
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
