---
id: cookbook
title: Cookbook
---

Here we list typical situations where we need to change the OCaml source code so that the translated code compiles in Coq.

## Abstractions in `.mli` files
When generating the Coq code, we do not use the notion of `.mli` because there are no such interface files in Coq. So the typical setup is to generate a `.v` file for each `.ml` file, and only translate the `.mli` files of the external dependencies to axiom files.

An issue in this process is that there can be differences between what a `.v` file sees and what a `.ml` file was seeing. For example, let us say that we have the following files:
* `a.ml`:
```ocaml
module type S = sig
  val pub : int -> int
end

module type S_internal = sig
  val pub : int -> int
  val priv : int -> int
end

module M : S_internal = struct
  let pub x = x + 1
  let priv x = x - 1
end
```
* `a.mli`:
```ocaml
module type S = sig
  val pub : int -> int
end

module M : S
```
* `b.ml`:
```ocaml
let f x = A.M.pub x
```
Then from the point of view of `b.ml`, `A.M` is of signature `A.S` and there are no ways to know about `A.S_internal`. However, in Coq, since we did not translate the `.mli` file, `A.M` appears as having the signature `S_internal`. Since we translate signatures to records, which do not have the notion of inclusion, `A.M` does not have the same type in Coq and OCaml. This can introduce bugs when we translate a signature annotation `S` to Coq, as Coq expects a signature `S_internal`.

A solution for this issue is to open the abstraction in `a.mli` by using the signature `S_internal` instead of `S`. A general solution on the side of `coq-of-ocaml` would be to translate the `.mli` to `.v` files doing the plumbing from `S` to `S_internal`. We have not done that yet, because of lack of time and because we believe that having `.v` files to do plumbing can also have a cost for the proofs.

## Fixpoint struct annotations
In Coq, fixpoints (recursive functions) must be structurally decreasing on one of the arguments to make sure that the function always terminates. When structural termination is not obvious, we can disable this check with the configuration option [without_guard_checking](configuration#without_guard_checking). However, Coq still requires to consider one of the parameters as the decreasing one, even if this is not structurally the case. A decreasing parameter is still required to know how far to unfold recursive definitions while doing proofs.

The way to specify the decreasing parameter is to use the attribute [coq_struct](attributes#coq_struct). For example we annotate the operator `-->` as follows:
```ocaml
let[@coq_struct "i"] rec ( --> ) i j =
  (* [i; i+1; ...; j] *)
  if Compare.Int.(i > j) then [] else i :: (succ i --> j)
```
Here `i` is decreasing when we consider the natural order on `-i`. This generates the following Coq code:
```coq
Fixpoint op_minusminusgt (i : int) (j : int) {struct i} : list int :=
  if i >i j then
    nil
  else
    cons i (op_minusminusgt (Pervasives.succ i) j).
```
The annotation `{struct i}` specifies in Coq that the decreasing parameter is `i`.

## Ignored functions
Sometimes definitions are too complex to translate to Coq, but we still want to go on with the rest of the files. A solution is to add the [coq_axiom_with_reason](attributes#coq_axiom_with_reason) to ignore a definition and replace it with an axiom of the same type.

For example, the following definition would not work in Coq as is it is, due to the use of GADTs:
```ocaml
  let fold_all f set acc =
    List.fold_left
      (fun acc (_, Ex_Kind kind) -> fold kind (f.f kind) set acc)
      acc
      all
```
We then add the attribute `@coq_axiom_with_reason`:
```ocaml
let fold_all f set acc =
    List.fold_left
      (fun acc (_, Ex_Kind kind) -> fold kind (f.f kind) set acc)
      acc
      all
    [@@coq_axiom_with_reason "gadt"]
```
This generates the following Coq code:
```coq
Axiom fold_all : forall {A : Set}, fold_f A -> t -> A -> A.
```
which compiles and has the right type, even if we lost the translation of the body of `fold_all`. With this attribute we must add a reason, so that we document we chose to introduce an axiom. Among frequent reasons are the use of GADTs and complex recursive functions.

## Mutual definitions as notations
Sometimes mutual definitions for a recursive function are used more as notations rather than to express a true mutual recursion. See the attribute [coq_mutual_as_notation](attributes#coq_mutual_as_notation) for more details about how to handle this kind of definition. Here is an example where this attribute is needed:
```ocaml
let rec double_list l =
  match l with
  | [] -> l
  | n :: l -> double n :: double_list l

and[@coq_mutual_as_notation] double n = 2 * n
```
which translates in Coq to:
```coq
Reserved Notation "'double".

Fixpoint double_list (l : list int) : list int :=
  let double := 'double in
  match l with
  | [] => l
  | cons n l => cons (double n) (double_list l)
  end

where "'double" := (fun (n : int) => Z.mul 2 n).

Definition double := 'double.
```

## Named signatures
We translate modules used in functors as records in Coq. We require a name for the signatures to have a name for the corresponding records. Sometimes, in OCaml, when a signature is used just once it is inlined and not named. Here is an example of code with an anonymous signature for the return signature of the functor `Make_indexed_carbonated_data_storage`:
```ocaml
module Make_indexed_carbonated_data_storage
    (C : Raw_context.T)
    (I : INDEX)
    (V : VALUE) : sig
  include
    Non_iterable_indexed_carbonated_data_storage
      with type t = C.t
       and type key = I.t
       and type value = V.t

  val list_values :
    ?offset:int ->
    ?length:int ->
    C.t ->
    (Raw_context.t * V.t list) tzresult Lwt.t
end = struct
  include Make_indexed_carbonated_data_storage_INTERNAL (C) (I) (V)
end
```
This generates the following error message in `coq-of-ocaml`:
```
--- storage_functors.ml:527:19 --------------------------------------------- not_supported (1/1) ---

  525 |     (C : Raw_context.T)
  526 |     (I : INDEX)
> 527 |     (V : VALUE) : sig
> 528 |   include
> 529 |     Non_iterable_indexed_carbonated_data_storage
> 530 |       with type t = C.t
> 531 |        and type key = I.t
> 532 |        and type value = V.t
> 533 | 
> 534 |   val list_values :
> 535 |     ?offset:int ->
> 536 |     ?length:int ->
> 537 |     C.t ->
> 538 |     (Raw_context.t * V.t list) tzresult Lwt.t
> 539 | end = struct
  540 |   include Make_indexed_carbonated_data_storage_INTERNAL (C) (I) (V)
  541 | end
  542 | 


Anonymous definition of signatures is not handled
```
We replace it by the following OCaml code, which translates into Coq without errors:
```ocaml
module type Non_iterable_indexed_carbonated_data_storage_with_values = sig
  include Non_iterable_indexed_carbonated_data_storage

  val list_values :
    ?offset:int ->
    ?length:int ->
    t ->
    (Raw_context.t * value list) tzresult Lwt.t
end

module Make_indexed_carbonated_data_storage
    (C : Raw_context.T)
    (I : INDEX)
    (V : VALUE) :
  Non_iterable_indexed_carbonated_data_storage_with_values
    with type t = C.t
     and type key = I.t
     and type value = V.t = struct
  include Make_indexed_carbonated_data_storage_INTERNAL (C) (I) (V)
end
```
There we named the return signature of the functor `Non_iterable_indexed_carbonated_data_storage_with_values`.

## Named polymorphic variant types
In the following OCaml code, the type of the parameter `depth` is a polymorphic variant type:
```ocaml
val fold :
  ?depth:[`Eq of int | `Le of int | `Lt of int | `Ge of int | `Gt of int] ->
  t ->
  key ->
  init:'a ->
  f:(key -> tree -> 'a -> 'a Lwt.t) ->
  'a Lwt.t
```
We do not handle this kind of type in `coq-of-ocaml`, because there are no clear equivalent features in Coq. In most of the code, we would replace this declaration with an algebraic datatype as follows:
```ocaml
type depth =
  | Eq of int
  | Le of int
  | Lt of int
  | Ge of int
  | Gt of int

val fold :
  ?depth:depth ->
  t ->
  key ->
  init:'a ->
  f:(key -> tree -> 'a -> 'a Lwt.t) ->
  'a Lwt.t
```
Sometimes it is not possible to do this kind of change, for backward compatibility of an API for example. In this case we name the polymorphic variant type:
```ocaml
type depth = [`Eq of int | `Le of int | `Lt of int | `Ge of int | `Gt of int]

val fold :
  ?depth:depth ->
  t ->
  key ->
  init:'a ->
  f:(key -> tree -> 'a -> 'a Lwt.t) ->
  'a Lwt.t
```
We translate the definition of `depth` as if it was an algebraic datatype:
```coq
Inductive depth : Set :=
| Ge : int -> depth
| Lt : int -> depth
| Eq : int -> depth
| Le : int -> depth
| Gt : int -> depth.
```
Then, using the configuration parameters [variant_constructors](configuration#variant_constructors) and [variant_types](configuration#variant_types), we instruct `coq-of-ocaml` to recognize that there is a type `depth` whenever it finds a constructor `` `Eq``, ..., or `` `Gt`` in the OCaml code.

## Nested anonymous signatures
There is support for nested anonymous signatures in `coq-of-ocaml`, but this often does not work well for various reasons. The key reason is that we translate signatures to records, which can only be flat. An example of a nested anonymous signature is the following:
```ocaml
module type TitleWithId = sig
  val title : string

  module Id : sig
    include ID

    module Temp : Temp_id with type t = private t
  end

  module IdSet : Set.S with type elt = Id.t
end
```
Here the signature of `Id` is anonymous and nested in the signature `TitleWithId`. By default, `coq-of-ocaml` will try to prefix all the fields of the sub-module `Id` by `Id_` and flatten these fields into the fields of `TitleWithId`:
```coq
Module TitleWithId.
  Record signature {Id_t IdSet_t : Set} : Set := {
    title : string;
    Id_t := Id_t;
    Id_compare : Id_t -> Id_t -> int;
    (* ... included fields from [ID] *)
    Id_Temp : Temp_id (t := t); (* there is an error: should be [(t := Id_t)] *)
    IdSet : _Set.S (elt := Id.(IdWithTemp.t)) (t := IdSet_t);
  }.
End TitleWithId.
Definition TitleWithId := @TitleWithId.signature.
Arguments TitleWithId {_ _}.
```
This works well if `Id` is used as a namespace in `TitleWithId` to group the fields in different categories. However, this fails if we aim to directly reference the sub-module `Id` later on.

A better solution is often to name the anonymous sub-signatures, by doing:
```ocaml
module type IdWithTemp = sig
  include ID

  module Temp : Temp_id with type t = private t
end

module type TitleWithId = sig
  val title : string

  module Id : IdWithTemp

  module IdSet : Set.S with type elt = Id.t
end
```
The translation is then:
```coq
Module IdWithTemp.
  Record signature {t : Set} : Set := {
    t := t;
    compare : t -> t -> int;
    (* ... included fields from [ID] *)
    Temp : Temp_id (t := t);
  }.
End IdWithTemp.
Definition IdWithTemp := @IdWithTemp.signature.
Arguments IdWithTemp {_}.

Module TitleWithId.
  Record signature {Id_t IdSet_t : Set} : Set := {
    title : string;
    Id : IdWithTemp (t := Id_t);
    IdSet : _Set.S (elt := Id.(IdWithTemp.t)) (t := IdSet_t);
  }.
End TitleWithId.
Definition TitleWithId := @TitleWithId.signature.
Arguments TitleWithId {_ _}.
```

## Non-mutually recursive types
Sometimes, because this is convenient, we use the syntax `type ... and` for types which are not mutually dependent. For example, we could write in OCaml:
```ocaml
type 'a matching_function = 'a -> match_result

and match_result = (string * int option) list
```
to show the definition of `matching_function` first. This example would not work in Coq because mutually recursive definitions have to be with at least one algebraic type definition. Even for cases where the translation works, having too many mutually recursive type definitions may complexify the proofs.

For all these reasons, it is better to only use the `and` keyword for types that are truly mutually recursive. In this case, we rewrite our example as:
```ocaml
type match_result = (string * int option) list

type 'a matching_function = 'a -> match_result
```

## Top-level name collisions
In Coq, it is not possible to have two definitions of the same name at top-level. For example, if we translate the following OCaml code:
```ocaml
let path = RPC_path.(open_root / "context" / "delegates")

let path = RPC_path.(path /: Signature.Public_key_hash.rpc_arg)
```
we get in Coq:
```coq
Definition path : RPC_path.path Updater.rpc_context Updater.rpc_context :=
  RPC_path.op_div (RPC_path.op_div RPC_path.open_root "context") "delegates".

Definition path
  : RPC_path.path Updater.rpc_context
    (Updater.rpc_context * Signature.public_key_hash) :=
  RPC_path.op_divcolon path
    Signature.Public_key_hash.(S.SIGNATURE_PUBLIC_KEY_HASH.rpc_arg).
```
which generates the error:
```
Error: path already exists.
```
A solution is to rename one of the two paths in OCaml:
```ocaml
let raw_path = RPC_path.(open_root / "context" / "delegates")

let path = RPC_path.(raw_path /: Signature.Public_key_hash.rpc_arg)
```
This kind of situation can also happen when including modules. For example, there is a collision if an included module has names that already exist at the current level. We believe this is a good thing that Coq forbids redefining names at top-level. So using `coq-of-ocaml` can be a good thing to forbid this practice in OCaml. Note however that it is still possible to redefine names inside an expression in Coq.
