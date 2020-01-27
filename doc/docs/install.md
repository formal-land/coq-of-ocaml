---
id: install
title: Install
---

We recommend you to install the latest stable version via [opam](https://opam.ocaml.org/).

## Latest stable version
Using the package manager opam, add the [Coq repository](http://coq.io/opam/):
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
```
and run:
```sh
opam install coq-of-ocaml
```
To check that it installed correctly, type:
```sh
coq-of-ocaml
```
It should show you the help message.

## Current development version
Clone the [GitHub repository](https://github.com/clarus/coq-of-ocaml) with the sources and run:
```sh
opam pin add coq-of-ocaml .
```

## Manually
Read the `coq-of-ocaml.opam` file at the root of the project to know the dependencies to install and to get the list of commands to build the project.
