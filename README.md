# ![Logo](https://clarus.github.io/coq-of-ocaml/img/rooster-48.png) coq-of-ocaml
> Import OCaml programs to Coq for formal verification

[![CI](https://github.com/clarus/coq-of-ocaml/workflows/CI/badge.svg?branch=master)](https://github.com/clarus/coq-of-ocaml/actions?query=workflow%3ACI)

**Documentation on https://clarus.github.io/coq-of-ocaml/**

## Aim
`coq-of-ocaml` aims to enable formal verification of [OCaml](https://ocaml.org/) programs&nbsp;🦄. The more you prove, the happier you are. By transforming OCaml code into similar [Coq](https://coq.inria.fr/) programs, it is possible to prove arbitrarily complex properties using the existing power of Coq. The sweet spot of `coq-of-ocaml` is purely functional and monadic programs. Side-effects outside of a monad, like references, and advanced features like object-oriented programming, may never be supported. By sticking to the supported subset of OCaml, you should be able to import millions of lines of code to Coq and write proofs at large. Running `coq-of-ocaml` after each code change, you can make sure that your proofs are still valid. We recommend organizing your proof files as you would organize your unit-test files.

The guiding idea of `coq-of-ocaml` is [TypeScript](https://www.typescriptlang.org/). Instead of bringing types to an untyped language, we bring proofs to an already typed language. The approach stays the same: finding the right sweet spot, using heuristics when needed, guiding the user with error messages. We use `coq-of-ocaml` at [Tezos](https://tezos.com/), a crypto-currency implemented in OCaml, in the hope to have near-zero bugs thanks to formal proofs. Tezos is currently one of the most advanced crypto-currencies, with smart contracts, proof-of-stake, encrypted transactions, and protocol upgrades. It aims to compete with Ethereum. Formal verification is claimed to be important for crypto-currencies as there are no central authorities to forbid bug exploits and a lot of money at stake. A Coq translation of the core components of Tezos is available in the project [coq-tezos-of-ocaml](https://gitlab.com/nomadic-labs/coq-tezos-of-ocaml). Protecting the money.

## Example
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
Require Import CoqOfOCaml.CoqOfOCaml.
Require Import CoqOfOCaml.Settings.

Inductive tree (a : Set) : Set :=
| Leaf : a -> tree a
| Node : tree a -> tree a -> tree a.

Arguments Leaf {_}.
Arguments Node {_}.

Fixpoint sum (tree : tree int) : int :=
  match tree with
  | Leaf n => n
  | Node tree1 tree2 => Z.add (sum tree1) (sum tree2)
  end.
```
You can now write proofs by induction over the `sum` function using Coq. To see how you can write proofs, you can simply look at the [Coq documentation](https://coq.inria.fr/documentation). Learning to write proofs is like learning a new programming paradigm. It can take time, but be worthwhile!

## Install
### Latest stable version
Using the package manager [opam](https://opam.ocaml.org/),
```
opam install coq-of-ocaml
```
### Current development version
To install the current development version:
```
opam pin add https://github.com/clarus/coq-of-ocaml.git#master
```

### Manually
Clone the Git submodule for [Merlin](https://github.com/ocaml/merlin):
```
git submodule init
git submodule update
```
Then read the `coq-of-ocaml.opam` file at the root of the project to know the dependencies to install and get the list of commands to build the project.

## Usage
The basic command is:
```
coq-of-ocaml file.ml
```
You can start to experiment with the test files in `tests/` or look at our [online examples](https://clarus.github.io/coq-of-ocaml/examples/). `coq-of-ocaml` compiles the `.ml` or `.mli` files using [Merlin](https://github.com/ocaml/merlin) to understand the dependencies of a project. One first needs to have a **compiled project** with a working configuration of Merlin. This is automatically the case if you use [dune](https://dune.build/) as a build system.

## Documentation
You can read the documentation on the website of the project at [https://clarus.github.io/coq-of-ocaml/](https://clarus.github.io/coq-of-ocaml/).

## Features
* the core of OCaml (functions, let bindings, pattern-matching,...) ✔️
* type definitions (records, inductive types, synonyms, mutual types) ✔️
* monadic programs ✔️
* modules as namespaces ✔️
* modules as polymorphic records (signatures, functors, first-class modules) ✔️
* multiple-file projects (thanks to Merlin) ✔️
* `.ml` and `.mli` files ✔️
* existential types (we use impredicative sets to avoid a universe explosion) ✔️
* partial support of GADTs 🌊
* partial support of polymorphic variants 🌊
* partial support of extensible types 🌊
* ignores side-effects outside of a monad ❌

Even in case of errors, we try to generate some Coq code along with an error message. The generated Coq code should be readable and with a size similar to the OCaml source. The generated Coq code does not necessarily compile after a first try. This can be due to various errors, such as name collisions. Do not hesitate to fix these errors by updating the OCaml source. If you want more assistance, contact us by creating an issue.

## License
MIT (open-source software)
