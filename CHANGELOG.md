## [Unreleased]
* Add configuration to add head suffix in the generated file.
* Add configuration to add monadic operators.
* Add configuration to specify dependencies required as mli files.
* Add configuration to list the required files in a file, together with an import or not.
* Add configuration to disable guard or positivity checking.
* Add handling of a configuration file.
* Add the `@coq_phantom` attribute to force an abstract type declaration to be phantom.

## 2.1.0 (March 20, 2020)
* Add automatic re-ordering of type synonyms in mutual types to generate valid definitions.
* Add minimal handling of class types as records.
* Ignore type parameters with constraints (like being a sub-type of some variants).
* Add a `@coq_struct "param"` attribute to specify the decreasing parameter name of fixpoints.
* Add a tactic `rewrite_cast_exists_eval_eq` to simplify the use of the `cast_exists` axiom in proofs.
* Name the arguments of the signatures.
* Rename `obj_magic` as `cast`.
* Set the primitive projection flag.
* Add support for the `with` operator on constructor records.
* Add an attribute `@coq_match_gadt_with_result` for GADT matches with casts for the results.
* Do not generate casts for the return values of the match branches with `@coq_match_gadt`.
* Remove the rarely used `match exception when false` construct for default return value in matches.
* Add arity annotations for the existentials.
* Eliminate phantom types and propagate this erasing.
* Inline the application operators `@@` and `|>`.
* Put first-class modules in `Set`, using existentials in impredicative sets.
* Add a `@coq_match_with_default` to generate a default branch for incomplete matches.
* Add a `@coq_force_gadt` attribute to force a type to be defined as a GADT (without type parameters).
* Add basic handling of module alias and typeof in `.mli` files.
* Add more type annotations on values to better support polymorphic values.
* Add better support for include of signatures in `.mli` files.
* Add support of `open` in `.mli` files.
* Upgrade to Coq 8.11.
* Add support for functors inside signatures.
* Add a special treatment with no axioms for the matching of algebraic types with existentials which are not GADTs (with the same type parameters for all the constructors).
* Add an annotation mechanism for implicits for Coq.
* Generate the JSON output in a default file.
* Optimize the execution time to find the name of a signature.
* Name the type of the records of constructors.
* Add an annotation mechanism to generate axioms for the `match` of GADTs.
* Use `record.(field)` to access record fields.
* Add an axiom for `assert`.
* Add basic support for includes of module types with sub-modules.
* Add `with` notation for records.
* Ignore patterns with extensible types.
* Replace the generation of `Export` by `Include` (fix).
* Add support of `include` in first-class module values.
* Add support of functor definitions.
* Add an annotation mechanism `[@axiom]` to ignore the content of some definitions.
* Use list notation for list values.
* Add support for `when` clauses in `match`.
* Disable recursivity checks in Coq.
* Change the include of signature to preserve the first-class sub-modules.
* Define a default value for the extensible types.
* Add support for constructors using records as parameters.
* Add polymorphic record fields for modules with polymorphic elements.
* Compute the shape of a module by only looking at the top-level of definitions.
* Add support of functor application.
* Use `let` to represent intermediate results in the definition of a first-class module value.
* Define modules with a named signature as dependent records.
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
