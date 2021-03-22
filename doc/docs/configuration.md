---
id: configuration
title: Configuration
---

We present the configuration mechanism of `coq-of-ocaml` to define some global settings. We write the configuration in a file in the [JSON format](https://www.json.org/json-en.html). To run `coq-of-ocaml` with a configuration file, use the `-config` option:
```sh
coq-of-ocaml -config configuration.json ...
```

The general structure of a configuration file is an object of entry keys and values:
```sh
{
  "entry_1": value_1,
  ...,
  "entry_n": value_n
}
```
An example is:
```json
{
  "error_message_blacklist": [
    "Unbound module Tezos_protocol_alpha_functor"
  ],
  "monadic_operators": [
    ["Error_monad.op_gtgteq", "let="],
    ["Error_monad.op_gtgteqquestion", "let=?"],
    ["Error_monad.op_gtgtquestion", "let?"]
  ],
  "require": [
    ["Tezos_raw_protocol_alpha", "Tezos"]
  ],
  "variant_constructors": [
    ["Dir", "Context.Dir"],
    ["Key", "Context.Key"],
    ["Hex", "MBytes.Hex"]
  ],
  "without_positivity_checking": [
    "src/proto_alpha/lib_protocol/storage_description.ml"
  ]
}
```
The configuration entries are described as follows.

## alias_barrier_modules
#### Example
```
"alias_barrier_modules": [
  "Tezos_protocol_environment_alpha__Environment"
]
```

#### Value
A list of module names at which to stop when iterating through record aliases to find the initial record definition.

#### Explanation
An example of OCaml code with a record alias is:
```ocaml
module A = struct
  type t = {a : string; b : bool}
end

module B = struct
  type t = A.t = {a : string; b : bool}
end

let x = {B.a = "hi"; b = true}
```
which generates:
```coq
Module A.
  Module t.
    Record record : Set := Build {
      a : string;
      b : bool }.
    Definition with_a a (r : record) :=
      Build a r.(b).
    Definition with_b b (r : record) :=
      Build r.(a) b.
  End t.
  Definition t := t.record.
End A.

Module B.
  Definition t : Set := A.t.
End B.

Definition x : B.t := {| A.t.a := "hi"; A.t.b := true |}.
```
Even if in OCaml we can talk about the field `B.a`, in Coq we transform it to `A.t.a` so that there is a single record definition. To do this transformation, we go through the record aliases up to the alias barriers, if any.

## constant_warning
#### Example
```
"constant_warning": false
```

#### Value
A boolean to select if there should be a warning in the generated code on some constants. A typical example are the integer constants which are all treated as `int`. The default of this option is `true`.

#### Explanation
Without setting this option to `false`, the output of the following code:
```ocaml
let n : int64 = 12L
```
is:
```coq
Definition n : int64 :=
  (* ❌ Constant of type int64 is converted to int *)
  12.
```
Setting the `constant_warning` option to `false` we get:
```coq
Definition n : int64 := 12.
```

## constructor_map
#### Example
```
"constructor_map": [
  ["public_key_hash", "Ed25519", "Ed25519Hash"],
  ["public_key_hash", "P256", "P256Hash"],
  ["public_key_hash", "Secp256k1", "Secp256k1Hash"]
]
```

#### Value
A list of triples with a type name, a constructor name and a new constructor name to rename to. The type name must be the type name associated to the constructor, and is not prefixed by a module name. This type name is mostly there to help to disambiguate.

#### Explanation
In OCaml we can have different types with the same constructor names, as long as the OCaml compiler can differentiate them based on type information. In Coq this is not the case. The definition of two constructors with the same name generates a name collision. For this reason, we can selectively rename some constructors in `coq-of-ocaml` in order to avoid name collisions in Coq.

## error_category_blacklist
#### Example
```
"error_category_blacklist": [
  "extensible_type",
  "module",
  "side_effect"
]
```

#### Value
A list of error categories to black-list. The category of an error message is given in its header. For example:
```
--- foo.ml:1:1 ------------------------------------------- side_effect (1/1) ---

> 1 | let () =
> 2 |   print_endline "hello world"
  3 | 


Top-level evaluations are ignored
```
is an error of category `side_effect`.

#### Explanation
We may want to ignore some categories of errors in order to focus on other errors in a CI system for example.

## error_filename_blacklist
#### Example
```
"error_filename_blacklist": [
  "src/proto_alpha/lib_protocol/alpha_context.ml",
  "src/proto_alpha/lib_protocol/alpha_context.mli"
]
```

#### Value
A list of file names on which not to fail, even in case of errors. The return code of `coq-of-ocaml` is then 0 (success). We still display the error messages.

#### Explanation
We may still want to see the error logs of some complicated files while not returning a fatal error.

## error_message_blacklist
#### Example
```
"error_message_blacklist": [
  "Unbound module Tezos_protocol_alpha_functor"
]
```

#### Value
A list of strings used to filtered out the error messages. An error message containing such a string is ignored.

#### Explanation
We may want to ignore an error after manual inspection. This option allows to ignore an arbitrary error based on its error message.

## escape_value
#### Example
```
"escape_value": [
  "a",
  "baking_rights_query",
  "json"
]
```

#### Value
A list of variable names to escape. We escape by replacing a name `foo` by `foo_value`. We do not escape type names or modules names.

#### Explanation
In OCaml, the value and type namespaces are different. For example, we can have a string named `string` of type `string`. In Coq, we need to find an alternate name in order to avoid a name collision. If you have a name collision due to a value having the same name as a type, you can use this option to escape the value name (and only the value name).

## first_class_module_path_blacklist
#### Example
```
"first_class_module_path_blacklist": [
  "Tezos_raw_protocol_alpha"
]
```

#### Value
A list of module names, typically corresponding to the module of a folder. All the modules which are direct children of such modules are considered as plain modules. They are encoded by Coq modules, even if there is a signature to make a corresponding record.

#### Explanation
The module system of `coq-of-ocaml` encodes the modules having a signature name as dependent records. We use the signature name as the record type name. Sometimes, for modules corresponding to files, we want to avoid using records even if there is a named signature. This option prevents the record encoding for modules of the form `A.B` where `A` is in the black-list. For example, when a reference to a value `A.B.c` appears, we generate `A.B.c` rather than `A.B.(signature_name_of_B.c)`. Indeed, `A.B` is a Coq module rather than a record.

## first_class_module_signature_blacklist
#### Example
```
"first_class_module_signature_blacklist": [
  "Sapling__Core_sig.T_encoding"
]
```

#### Value
A list of OCaml signature names. We ignore these signatures when looking for a signature name to encode modules as records.

#### Explanation
In `coq-of-ocaml`, we look for a named signature for each module we encounter. Once we find a named signature we encode the module as a dependent record. If no signatures can be found, we use a plain Coq module. Sometimes, we find an incorrect signature as we use heuristics to find a matching signature. This configuration option helps to ignore incorrect signatures.

## head_suffix
#### Example
```
"head_suffix": "Import Environment.Notations.\n"
```

#### Value
A string to add in the header of each file.

#### Explanation
We can use this option to add some default imports, or turn on some notations or flags.

## merge_returns
#### Example
```
"merge_returns": [
  ["return=", "return?", "return=?"]
]
```

#### Value
A list of triple of strings, with two return operator names which get translated into a third when applied together.

#### Explanation
We use this configuration option to merge two return operators to a third equivalent one. Note that this only applies to monadic return operators, which are generated by the monadic configuration options. This option does not apply to standard function applications. As an example, we can generate the following code:
```coq
let= ctxt :=
  (|Storage.Contract.Frozen_rewards|).(Storage_sigs.Indexed_data_storage.remove)
    (ctxt, contract) cycle in
return=?
  (ctxt,
    {| frozen_balance.deposit := deposit; frozen_balance.fees := fees;
      frozen_balance.rewards := rewards |}).
```
instead of:
```coq
let= ctxt :=
  (|Storage.Contract.Frozen_rewards|).(Storage_sigs.Indexed_data_storage.remove)
    (ctxt, contract) cycle in
return=
  (return?
    (ctxt,
      {| frozen_balance.deposit := deposit; frozen_balance.fees := fees;
        frozen_balance.rewards := rewards |})).
```

## merge_types
#### Example
```
"merge_types": [
  ["M=", "M?", "M=?"]
]
```

#### Value
A list of triple of strings, with two type names which get translated into a third when applied together.

#### Explanation
We use this configuration option for very specific use cases. It allows to merge two types together for when there is a more convenient notation. For example, we can generate the following code:
```coq
Definition burn_storage_fees
  (c : Raw_context.t) (storage_limit : Z.t) (payer : Contract_repr.t)
  : M=? Raw_context.t :=
```
instead of:
```coq
Definition burn_storage_fees
  (c : Raw_context.t) (storage_limit : Z.t) (payer : Contract_repr.t)
  : M= (M? Raw_context.t) :=
```

## monadic_lets
#### Example
```
"monadic_lets": [
  ["Error_monad.op_gtgteq", "let="],
  ["Error_monad.op_gtgteqquestion", "let=?"],
  ["Error_monad.op_gtgtquestion", "let?"]
]
```

#### Value
A list of couples of a monadic bind name and a monadic notation to use by `coq-of-ocaml`. You still have to define the notations somewhere, such as:
```coq
Notation "'let?' x ':=' X 'in' Y" :=
  (Error_monad.op_gtgtquestion X (fun x => Y))
  (at level 200, x ident, X at level 100, Y at level 200).

Notation "'let?' ' x ':=' X 'in' Y" :=
  (Error_monad.op_gtgtquestion X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).
```
The binder `x` can be a variable name or a pattern prefixed by `'`.

#### Explanation
This helps to improve readability of code with effects written in a monadic style. For example:
```ocaml
(* let (>>=) x f = ... *)

let operate x =
  operation1 x >>= fun (y, z) ->
  operation2 y z
```
will generate, thanks to the notation mechanism:
```coq
Definition operate (x : string) : int :=
  let! '(y, z) := operation1 x in
  operation2 y z.
```
Note that you can also use the monadic notation in OCaml with the [binding operators](https://caml.inria.fr/pub/docs/manual-ocaml/bindingops.html).

## monadic_let_returns
#### Example
```
"monadic_let_returns": [
  ["Error_monad.op_gtpipeeq", "let=", "return="],
  ["Error_monad.op_gtpipeeqquestion", "let=?", "return=?"],
  ["Error_monad.op_gtpipequestion", "let?", "return?"]
]
```

#### Value
A list of triples of a function name, a monadic notation for a binder and a return function.

#### Explanation
This allows to rewrite a monadic map operator as a combination of a monadic `let` and `return`. For example, we can translate:
```ocaml
(* map : 'a m -> ('a -> 'b) -> 'b m *)
(* f : 'a m -> 'a m *)

let example x =
  map (f x) (fun x -> x + 1)
```
to:
```coq
Definition example (x : m int) : m int :=
  let! x := f x in
  return! (Z.add x 1).
```

## monadic_returns
#### Example
```
"monadic_returns": [
  ["Lwt._return", "return="],
  ["Error_monad._return", "return=?"],
  ["Error_monad.ok", "return?"]
]
```

#### Value
A list of couples of a function name and a return function.

#### Explanation
This allows to rewrite a return function as a return operator. For example, we can rewrite:
```ocaml
type 'a m = 'a * int

let return (x : 'a) : 'a m =
  (x, 0)

let incr x =
  return (x + 1)
```
to:
```coq
Definition m (a : Set) : Set := a * int.

Definition _return {a : Set} (x : a) : m a := (x, 0).

Definition incr (x : int) : m int := return! (Z.add x 1).
```
To define we return notation, we use:
```coq
Notation "return! X" := (_return X) (at level 20).
```
We add this notation by hand, as opposed to generate it in with `coq-of-ocaml`. Note that we use a notation for the return operator applied to some argument `X`. This is to have a correct syntax highlighting in the generated documentation with `coqdoc`. The following notation:
```coq
Notation "return!" := _return.
```
would not generate the correct coloration with our current Coq version (8.12).

## monadic_return_lets
#### Example
```
"monadic_return_lets": [
  ["Error_monad.op_gtgtquestioneq", "return=", "let=?"]
]
```

#### Value
A list of triples of a function name, a return function and a monadic notation for a binder.

#### Explanation
This allows to rewrite a monadic code with a special operator of the form:
```ocaml
operator e1 (fun x -> e2)
```
to:
```coq
let! x := return? e1 in
e2
```

## operator_infix
#### Example
```
"operator_infix": [
  ["Int32.add", "+i32"],
  ["Int32.sub", "-i32"],
  ["Int32.mul", "*i32"],
  ["Int32.div", "/i32"]
]
```

#### Value
A list of couples of an operator name and its notation.

#### Explanation
In order to generate readable code, for example for arithmetic expressions, we may want to use infix operators. For example, in our code we were able to go from:
```coq
let all_votes := Int32.add casted_votes ballots.(Vote_storage.ballots.pass) in
let supermajority := Int32.div (Int32.mul 8 casted_votes) 10 in
let participation :=
  Int64.to_int32
    (Int64.div (Int64.mul (Int64.of_int32 all_votes) 10000)
      (Int64.of_int32 maximum_vote)) in
let approval :=
  Pervasives.op_andand
    ((|Compare.Int32|).(Compare.S.op_gteq) participation expected_quorum)
    ((|Compare.Int32|).(Compare.S.op_gteq) ballots.(Vote_storage.ballots.yay)
...
```
to:
```coq
let all_votes := casted_votes +i32 ballots.(Vote_storage.ballots.pass) in
let supermajority := (8 *i32 casted_votes) /i32 10 in
let participation :=
  Int64.to_int32
    (((Int64.of_int32 all_votes) *i64 10000) /i64
    (Int64.of_int32 maximum_vote)) in
let approval :=
  (participation >=i32 expected_quorum) &&
  (ballots.(Vote_storage.ballots.yay) >=i32 supermajority) in
...
```
using infix operators. We believe the second form to be much more readable.

Note that you need to define the notations by writing some Coq code. For example, for the `int32` notations we used:
```coq
Infix "+i32" := Int32.add (at level 50, left associativity).
Infix "-i32" := Int32.sub (at level 50, left associativity).
Infix "*i32" := Int32.mul (at level 40, left associativity).
Infix "/i32" := Int32.div (at level 40, left associativity).
```
There should be no bugs due to the precedence of the operators, as we always parenthesis in case of doubt. However, having the right precedence may be nice when doing the proofs and pretty-printing terms. A good way to know about the precedences is to look at the reserved operator of the [standard library of Coq](https://coq.inria.fr/library/Coq.Init.Notations.html).

## renaming_rules
#### Example
```
"renaming_rules": [
  ["Stdlib.result", "sum"],
  ["Stdlib.List.map", "List.map"],
  ["Stdlib.List.rev", "List.rev"]
]
```

#### Value
A list of couple of values, with a name and a name to rename to while doing the translation in Coq.

#### Explanation
We may want to systematically rename some of the OCaml values to their counterpart in Coq. This rule applies to anything which has a name (value, type, module, constructor, ...). `coq-of-ocaml` already knows some renaming rules for the OCaml's standard library, but it is possible to add more with this option.

## renaming_type_constructor
#### Example
```
"renaming_type_constructor": [
  ["(|Compare.Char|).(Compare.S.t)", "ascii"],
  ["(|Compare.Int|).(Compare.S.t)", "int"],
  ["(|Compare.Int32|).(Compare.S.t)", "int32"],
  ["(|Compare.Int64|).(Compare.S.t)", "int64"],
  ["(|Compare.String|).(Compare.S.t)", "string"],
  ["(|Compare.Z|).(Compare.S.t)", "Z.t"]
],
```

#### Value
A list of couples of a type constructor's name and a new name to rename to.

#### Explanation
In order to shorten the size of the generated Coq, we may want to rename some of the types. This is for example the case of types inside modules, like in the example above.

## require
#### Example
```
"require": [
  ["Tezos_raw_protocol_alpha", "Tezos"]
]
```

#### Value
A list of couples of a module name and a module to require from in Coq.

#### Explanation
When we import a project with many files in Coq, we need to add the relevant `Require` directives for external references. For a require rule `["A", "B"]`, when we see in OCaml a reference to the module `A.M`, we generate in Coq the reference `M`. We also add a `Require B.M.` at the top of the file.

## require_import
#### Example
```
"require_import": [
  ["Tezos_protocol_environment_alpha", "Tezos"]
]
```

#### Value
A list of couples of a module name and a module to require import from in Coq.

#### Explanation
Similar to the `require` command, with an additional `Import` in order to shorten the paths for commonly used modules.

## require_long_ident
#### Example
```
"require_long_ident": [
  ["Storage_description", "Tezos"]
]
```

#### Value
A list of module names and module namespaces to require from.

#### Explanation
In some cases, it is not possible to get the right `Require` directive for an external reference. In particular when there is a long identifier rather than a path in the OCaml AST. With a rule `["A", "B"]`, a reference to the module `A` also generates the same reference `A` but adds a `Require B.A.` at the top of the output.

## require_mli
#### Example
```
"require_mli": [
  "Storage",
  "Storage_functors"
]
```

#### Value
A list of files to require as `.mli` rather than as `.ml`. The files are described by their corresponding module name.

#### Explanation
In OCaml, there are two kinds of files, namely `.ml` and `.mli` files. We import both with `coq-of-ocaml`, but only the `.ml` file is complete and sufficient. The `.mli` import corresponds to axioms without the definitions. However, sometimes the import of the `.ml` version fails but the `.mli` works. Then, we may want to use the imported `.mli` as a dependency in the `Require` directive rather than the imported `.ml` version.

## variant_constructors
#### Example
```
"variant_constructors": [
  ["Dir", "Context.Dir"],
  ["Key", "Context.Key"],
  ["Uint16", "Data_encoding.Uint16"],
  ["Uint8", "Data_encoding.Uint8"],
  ["Hex", "MBytes.Hex"]
]
```

#### Value
A list of polymorphic variant constructor names in OCaml and constructor names in Coq.

#### Explanation
Coq supports algebraic types through the `Inductive` keyword, but there are no direct equivalents for [polymorphic variants](https://caml.inria.fr/pub/docs/manual-ocaml/lablexamples.html#s:polymorphic-variants). We can replace many occurrences of polymorphic variants by standard algebraic types, updating the input code to help `coq-of-ocaml`. Sometimes, a direct modification of the source is not possible. We can then explain to `coq-of-ocaml` how to deal with polymorphic variants as if they were inductive types.

When there is a type definition with a polymorphic variant, `coq-of-ocaml` transforms it to the closest inductive:
```ocaml
module Context = struct
  type t = [`Dir | `Key]
end
```
generates:
```coq
Module Context.
  Inductive t : Set :=
  | Dir : t
  | Key : t.
End Context.
```
When a constructor appears, this option helps to tell Coq from which module it is. For example:
```ocaml
let x : Context.t = `Dir
```
would be transformed to:
```coq
Definition x : Context.t := Dir.
```
which is incorrect. By giving the relation `["Dir", "Context.Dir"]`, we can tell `coq-of-ocaml` to generate the correct constructor with the correct module prefix:
```coq
Definition x : Context.t := Context.Dir.
```

## variant_types
#### Example
```
"variant_types": [
  ["Dir", "Context.key_or_dir"],
  ["Key", "Context.key_or_dir"]
]
```

#### Value
A list of couples of a polymorphic variant constructor and a type name to use when the constructor appears.

#### Explanation
When we name a polymorphic variant with a type synonym:
```ocaml
type t = [`Dir | `Key]
```
an expression could still have a type without mentioning `t`:
```ocaml
let x : [`Dir] = `Dir
```
Since the polymorphic variants do not have a direct equivalent in OCaml, we could instead use a standard algebraic type:
```ocaml
type t = Dir | Key

let x : t = Dir
```
which translates to:
```coq
Inductive t : Set :=
| Dir : t
| Key : t.

Definition x : t := Dir.
```

When removing polymorphic variants is not possible, `coq-of-ocaml` transforms the type definition to the closest inductive type:
```coq
Inductive t : Set :=
| Dir : t
| Key : t.
```
and with the setting `["Dir", "t"]` it also correctly transforms the type of `x`:
```coq
Definition x : t := Dir.
```

## without_guard_checking
#### Example
```
"without_guard_checking": [
  "src/proto_alpha/lib_protocol/apply.ml",
  "src/proto_alpha/lib_protocol/misc.ml",
  "src/proto_alpha/lib_protocol/raw_context.ml",
  "src/proto_alpha/lib_protocol/script_interpreter.ml",
  "src/proto_alpha/lib_protocol/storage_description.ml"
]
```

#### Value
A list of filenames on which to disable termination checks by Coq.

#### Explanation
This option turns off the flag `Guard Checking`:
```coq
Unset Guard Checking.
```
Thus it is possible to write fixpoints which are not syntactically terminating. To help the evaluation tactics to terminate in the proofs, we can combine this setting with the [coq_struct](http://localhost:3000/coq-of-ocaml/docs/attributes#coq_struct) attribute.

For example, the following OCaml code:
```ocaml
(* let split_at (c : char) (s : string) : (string * string) option = ... *)

let rec split_all (c : char) (s : string) : string list =
  match split_at c s with
  | None -> [s]
  | Some (s1, s2) -> s1 :: split_all c s2
```
generates:
```coq
Fixpoint split_all (c : ascii) (s : string) : list string :=
  match split_at c s with
  | None => [ s ]
  | Some (s1, s2) => cons s1 (split_all c s2)
  end.
```
which is not accepted by Coq with the error:
```
Error: Cannot guess decreasing argument of fix.
```
despite the fact that we know that `split_at` should always return a smaller string. By disabling the guard checking, we can force Coq to accept this example of code. We automatically add a `struct` annotation on the first fixpoint argument so that Coq accepts the definition:
```coq
Fixpoint split_all (c : ascii) (s : string) {struct c} : list string :=
  match split_at c s with
  | None => [ s ]
  | Some (s1, s2) => cons s1 (split_all c s2)
  end.
```
However, we must be cautious as a `struct` annotation may break the symbolic evaluation of `split_all` since `c` never changes in recursive calls. For example:
```coq
Parameter P : ascii -> string -> list string -> Prop.

Lemma split_all_property (c : ascii) (s : string) : P c s (split_all c s).
  destruct c; simpl.
```
produces:
```
Error: Stack overflow.
```
because `split_all` is infinitely unfolded. With the `coq_struct` attribute we can force the `struct` annotation to be on the argument `s`:
```ocaml
let rec split_all (c : char) (s : string) : string list =
  match split_at c s with
  | None -> [s]
  | Some (s1, s2) -> s1 :: split_all c s2
[@@coq_struct "s"]
```
produces:
```coq
Fixpoint split_all (c : ascii) (s : string) {struct s} : list string :=
  match split_at c s with
  | None => [ s ]
  | Some (s1, s2) => cons s1 (split_all c s2)
  end.
```
Then, neither:
```coq
destruct c; simpl.
```
nor:
```coq
destruct s; simpl.
```
breaks. For more information about the reduction strategies in Coq proofs, you can start with the documentation of the [simpl tactic](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.simpl).

## without_positivity_checking
#### Example
```
"without_positivity_checking": [
  "src/proto_alpha/lib_protocol/storage_description.ml"
]
```

#### Value
A list of filenames on which to disable the positivity checking.

#### Explanation
This option turns off the flag `Positivity Checking`:
```coq
Unset Positivity Checking.
```
This allows to define types which would not respect the strict positivity condition:
```ocaml
type t = L of (t -> t)
```
generates:
```coq
Inductive t : Set :=
| L : (t -> t) -> t.
```
which without this setting gives this error in Coq:
```
Error: Non strictly positive occurrence of "t" in "(t -> t) -> t".
```
