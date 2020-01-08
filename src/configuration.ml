let without_positivity_checking = [
  "storage_description.ml";
]

let without_guard_checking = [
  "apply.ml";
  "apply_results.ml";
  "baking.ml";
  "contract_repr.ml";
  "legacy_script_support_repr.ml";
  "level_storage.ml";
  "michelson_v1_gas.ml";
  "michelson_v1_primitives.ml";
  "misc.ml";
  "operation_repr.ml";
  "qty_repr.ml";
  "raw_context.ml";
  "roll_storage.ml";
  "script_interpreter.ml";
  "script_ir_annot.ml";
  "script_ir_translator.ml";
  "script_repr.ml";
  "seed_repr.ml";
  "storage_description.ml";
  "storage_functors.ml";
]

let is_guard_checking_disabled = ref false
