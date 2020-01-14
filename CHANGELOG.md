## [Unreleased]
* Handle `include` in signatures of `.mli` files.
* Wrap records into modules to prevent name collisions with projections.
* Add support for polymorphic abstract types in modules.
* Put more generated errors as comments to allow partial compilation.
* Add support for module declarations with an anonymous signature in `.mli` files (by unfolding the signature).
* Add support for module type definitions in `.mli` files.
* Generate inductive type definitions for type definitions as polymorphic variants.
* Convert inlined polymorphic variant types to sum types with annotations in comments.
* Have a mechanism to lift some value names independently of type names to prevent name collisions.
* Use `Set` instead of `Type` (may require to use the `-impredicative-set` flag to compile generated files).
* Reduce the number of parenthesis in generated types using the precedence of the type operators.

## 2.0.0 (December 15, 2019)
* First public release financed by [Nomadic Labs](https://www.nomadic-labs.com/).
