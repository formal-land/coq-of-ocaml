---
id: examples
title: Examples
---

The main project handled with `coq-of-ocaml` is the crypto-currency [Tezos](https://tezos.com/). The result is in the project:
* `coq-tezos-of-ocaml`: https://nomadic-labs.gitlab.io/coq-tezos-of-ocaml/

providing a translation in Coq of the economic protocol of Tezos. You can also look at the [historical result](https://clarus.github.io/coq-of-ocaml/examples/tezos/) of the first compiling translation of the protocol of Tezos.

We are now focusing on:
* maintaining the translation of the protocol of Tezos, as the protocol evolves;
* improving this translation by removing some (supposedly safe) axioms;
* applying `coq-of-ocaml` to other OCaml programs.
