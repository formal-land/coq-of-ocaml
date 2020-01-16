## [Unreleased]
* Add changelog file.
* Add support for `include` of modules represented as a record.
* Fix bug on ambiguous detection of first-class module signatures.
* Ignore top-level `let () = ...` and the left-hand side of expression sequences `... ; ...`.
* Capitalize generated file names.
* Add the notation `record.[field]` to access to records with existential types.
* Use tuples with primitive projections for the tuples of existential types in first-class modules (notation `[x, y, z]` for the values, `[X * Y * Z]` for the types).
* Only use the value names to infer a module type name to handle destructive type substitutions (`:=` operator).
* Add support for functor declarations.
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
