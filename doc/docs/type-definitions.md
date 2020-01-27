---
id: type-definitions
title: Type definitions
---

Coq-of-ocaml generates the Coq definitions corresponding to OCaml's type definitions.

## Single type definitions
### Synonyms
Type synonyms are transformed to Coq definitions:
```ocaml
type string_list = string list
```
generates:
```coq
Definition string_list := list string.
```

### Records
OCaml records are transformed to Coq records, namespaced into a module to prevent name collisions. The transformation includes the `with_` operators for field substitutions:
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

### Algebraic data types
Algebraic data types generate an inductive definition in Coq:
```ocaml
type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree
```
generates:
```coq
Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : (tree a) -> (tree a) -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.
```
For data constructors with a record parameter, the convention (from the OCaml compiler) is to name the corresponding record `type.Constructor`:
```ocaml
type element =
  | Point of { x : int; y : int}
  | Rectangle of { height : int; width : int}
```
generates:
```coq
Module element.
  Module Point.
    Record record {x y : Set} := {
      x : x;
      y : y }.
    Arguments record : clear implicits.
  End Point.
  Definition Point := Point.record.
  
  Module Rectangle.
    Record record {height width : Set} := {
      height : height;
      width : width }.
    Arguments record : clear implicits.
  End Rectangle.
  Definition Rectangle := Rectangle.record.
End element.

Inductive element : Set :=
| Point : element.Point Z Z -> element
| Rectangle : element.Rectangle Z Z -> element.
```
The definitions of the constructors' records are polymorphic so that they can be applied to the type being defined if needed (in this case `element`).

### Extensible types
The various forms of extensible types are ignored:
```ocaml
exception Too_long of string
```
generates:
```coq
(* exception Too_long *)
```
and:
```ocaml
type error += Lazy_script_decode
```
generates:
```coq
(* type_extension *)
```

### Polymorphic variants
The polymorphic variant types are converted to the corresponding Coq inductive as an approximation:
```ocaml
type json =
  [ `O of (string * json) list
  | `Bool of bool
  | `Float of float
  | `A of json list
  | `Null
  | `String of string ]
```
generates:
```coq
Inductive json : Set :=
| Bool : bool -> json
| Null : json
| O : list (string * json) -> json
| Float : Z -> json
| String : string -> json
| A : list json -> json.
```

## Mutually recursive types
Coq only accept mutually recursive types on inductive definitions. A known trick is to use a Coq notation to simulate mutual definitions with type synonyms:
```ocaml
type path = path_item list

and path_item =
  | Field of string  (** A field in an object. *)
  | Index of int  (** An index in an array. *)
  | Star  (** Any / every field or index. *)
```
generates:
```coq
Reserved Notation "'path".

Inductive path_item : Set :=
| Index : Z -> path_item
| Field : string -> path_item
| Star : path_item

where "'path" := (list path_item).

Definition path := 'path.
```
For mutual definitions with a record, coq-of-ocaml first generate record skeletons, so that the record definitions are transformed into type synonyms:
```ocaml
type 'o t =
  [ `Ok of 'o (* 200 *)
  | `OkStream of 'o stream (* 200 *)
  | `Error of error list option (* 500 *) ]

and 'a stream = {next : unit -> 'a option Lwt.t; shutdown : unit -> unit}
```
generates:
```coq
Reserved Notation "'stream".

Module stream.
  Record record {next shutdown : Set} := {
    next : next;
    shutdown : shutdown }.
  Arguments record : clear implicits.
  Definition with_next {next_type shutdown_type : Set}
    (r : record next_type shutdown_type) next
    : record next_type shutdown_type :=
    {| next := next; shutdown := shutdown r |}.
  Definition with_shutdown {next_type shutdown_type : Set}
    (r : record next_type shutdown_type) shutdown
    : record next_type shutdown_type :=
    {| next := next r; shutdown := shutdown |}.
End stream.
Definition stream_skeleton := stream.record.

Inductive t (o : Set) : Set :=
| OkStream : 'stream o -> t o
| Ok : o -> t o
| Error : option (list Error_monad.__error) -> t o

where "'stream" := (fun (a : Set) =>
  stream_skeleton (unit -> Lwt.t (option a)) (unit -> unit)).

Definition stream := 'stream.

Arguments OkStream {_}.
Arguments Ok {_}.
Arguments Error {_}.
```

## GADTs
