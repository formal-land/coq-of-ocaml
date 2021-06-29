---
id: cookbook
title: Cookbook
---

Here we list typical situations where we need to change the OCaml source code so that the translated code compiles in Coq.

## Fixpoint struct annotations
In Coq, fixpoints (recursive functions) must be structurally decreasing on one of the arguments in order to make sure that the function always terminates. When structural termination is not obvious, we can disable this check with the configuration option [without_guard_checking](configuration#without_guard_checking). However, Coq still requires to consider one of the parameter as the decreasing one, even if this is not structurally the case. A decreasing parameter is still required to know how far to unfold recursive definitions while doing proofs.

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

## Mutual definitions as notations
Sometimes mutual definitions for a recursive function are used more as notations rather than to express a true mutual recursion. See the attribute [coq_mutual_as_notation](attributes#coq_mutual_as_notation) for more details about how to handle this kind of definitions. Here is an example where this attribute is needed:
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

## Nested signatures
There is a support for nested anonymous signatures in `coq-of-ocaml`, but this often does not work well for various reasons. The key reason is that we translate signatures to records, which can only be flat. An example of nested anonymous signature is the following:
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

## Non-mutually recursive definitions
Sometimes we use the `and` keyword for definitions which are not mutually recursive:
```ocaml
let numbits x =
  let x = ref x and n = ref 0 in
  (* ... *)
```
Since we do not check if the definitions are truly mutually recursive, `coq-of-ocaml` would generate the following Coq code:
```coq
Definition numbits (x : int) : int :=
  let x : Stdlib.ref int :=
    Stdlib.ref_value x
  with n : Stdlib.ref int :=
    Stdlib.ref_value 0 in
  (* ... *)
```
on which Coq fails because the `with` keyword only works for mutually recursive definitions. The solution is then to explicit that `x` and `n` are not mutually recursive:
```ocaml
let numbits x =
  let x = ref x in
  let n = ref 0 in
  (* ... *)
```

## Non-mutually recursive types
Sometimes, because this is convenient, we use the syntax `type ... and` for types which are actually not mutually dependent. For example we could write in OCaml:
```ocaml
type 'a matching_function = 'a -> match_result

and match_result = (string * int option) list
```
to show the definition of `matching_function` first. This example would not work in Coq because mutually recursive definitions have to be with at least one algebraic type definition. Even for cases where the translation works, having too many mutually recursive type definitions may complexify the proofs.

For all these reasons, it is better to only use the `and` keyword for types which are truly mutually recursive. In this case, we rewrite our example as:
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
This kind of situation can also happen when including modules. For example, there is a collision if an included module has names which already exist at the current level. We believe this is a good thing that Coq forbids redefining names at top-level. So using `coq-of-ocaml` can be a good thing to forbid this practice in OCaml. Note however that it is still possible to redefine names inside an expression in Coq.
