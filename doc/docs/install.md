---
id: install
title: Install
---

We recommend to install the latest stable version of `coq-of-ocaml` via [opam](https://opam.ocaml.org/).

## Latest stable version
Using the package manager `opam`, run:
```sh
opam install coq-of-ocaml
```
To check that it installed correctly, type:
```sh
coq-of-ocaml
```
It should show you the help message.

## Current development version
Install the development version to get the latest features. Clone the [GitHub repository](https://github.com/clarus/coq-of-ocaml) with the sources and run in the root folder of the project:
```sh
opam pin add coq-of-ocaml .
```

## Manually
Read the `coq-of-ocaml.opam` file at the root of the project to know the updated list of dependencies of the project and commands to build it.
