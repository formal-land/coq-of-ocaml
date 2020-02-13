# ![Logo](https://clarus.github.io/coq-of-ocaml/img/rooster-48.png) coq-of-ocaml
> Import OCaml programs to Coq.

[![travis status](https://img.shields.io/travis/clarus/coq-of-ocaml/master.svg?label=travis-ci)](https://travis-ci.org/clarus/coq-of-ocaml)
[![Join the chat at https://gitter.im/clarus/coq-of-ocaml](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/clarus/coq-of-ocaml?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

**https://clarus.github.io/coq-of-ocaml/**

Start with the file `main.ml`:
```ocaml
type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree

let rec sum tree =
  match tree with
  | Leaf n -> n
  | Node (tree1, tree2) -> sum tree1 + sum tree2
```

Run:
```
coq-of-ocaml main.ml
```

Get a file `Main.v`:
```coq
Require Import OCaml.OCaml.

Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : tree a -> tree a -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Fixpoint sum (tree : tree Z) : Z :=
  match tree with
  | Leaf n => n
  | Node tree1 tree2 => Z.add (sum tree1) (sum tree2)
  end.
```

## Features
* core of OCaml (functions, let bindings, pattern-matching,...) ✔️
* type definitions (records, inductive types, synonyms, mutual types) ✔️
* modules as namespaces ✔️
* modules as dependent records (signatures, functors, first-class modules) ✔️
* projects with complex dependencies using `.merlin` files ✔️
* `.ml` and `.mli` files ✔️
* existential types ✔️
* partial support of GADTs 🌊
* partial support of polymorphic variants 🌊
* ignores extensible types ❌
* ignores side-effects ❌

Even in case of errors we try to generate some Coq code. The generated Coq code should be readable and with a size similar to the OCaml source. One should not hesitate to fix remaining compilation errors, by hand or with a script (name collisions, missing `Require`,...).

## Install
### Latest stable version
Using the package manager [opam](https://opam.ocaml.org/), add the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-of-ocaml

### Current development version
To install the current development version:
```
opam pin add https://github.com/clarus/coq-of-ocaml.git#master
```

### Manually
Read the `coq-of-ocaml.opam` file at the root of the project to know the dependencies to install and get the list of commands to build the project.

## Usage
`coq-of-ocaml` compiles the `.ml` or `.mli` files using [Merlin](https://github.com/ocaml/merlin) to understand the dependencies of a project. One first needs to have a **compiled project** with a working configuration of Merlin. The basic command is:
```
coq-of-ocaml file.ml
```

If this does not work as expected, you may specify the path to a `.merlin` file:
```
coq-of-ocaml -merlin src/.merlin path/file.ml
```

You can start to experiment with the test files in `tests/` or look at our [online examples](https://clarus.github.io/coq-of-ocaml/examples/).

## License
MIT © Guillaume Claret.
