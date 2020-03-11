(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Tezos.Environment.
Import Environment.Notations.
Require Tezos.Constants_repr.
Require Tezos.Fitness_repr.
Require Tezos.Nonce_hash.

Module contents.
  Record record : Set := Build {
    priority : int;
    seed_nonce_hash : option Nonce_hash.t;
    proof_of_work_nonce : MBytes.t }.
  Definition with_priority priority (r : record) :=
    Build priority r.(seed_nonce_hash) r.(proof_of_work_nonce).
  Definition with_seed_nonce_hash seed_nonce_hash (r : record) :=
    Build r.(priority) seed_nonce_hash r.(proof_of_work_nonce).
  Definition with_proof_of_work_nonce proof_of_work_nonce (r : record) :=
    Build r.(priority) r.(seed_nonce_hash) proof_of_work_nonce.
End contents.
Definition contents := contents.record.

Module protocol_data.
  Record record : Set := Build {
    contents : contents;
    signature : Signature.t }.
  Definition with_contents contents (r : record) :=
    Build contents r.(signature).
  Definition with_signature signature (r : record) :=
    Build r.(contents) signature.
End protocol_data.
Definition protocol_data := protocol_data.record.

Module block_header.
  Record record : Set := Build {
    shell : Block_header.shell_header;
    protocol_data : protocol_data }.
  Definition with_shell shell (r : record) :=
    Build shell r.(protocol_data).
  Definition with_protocol_data protocol_data (r : record) :=
    Build r.(shell) protocol_data.
End block_header.
Definition block_header := block_header.record.

Definition raw : Set := Block_header.t.

Definition shell_header : Set := Block_header.shell_header.

Definition raw_encoding : Data_encoding.t Block_header.t :=
  Block_header.encoding.

Definition shell_header_encoding : Data_encoding.t Block_header.shell_header :=
  Block_header.shell_header_encoding.

Definition contents_encoding : Data_encoding.encoding contents :=
  (let arg := Data_encoding.def "block_header.alpha.unsigned_contents" in
  fun eta => arg None None eta)
    (Data_encoding.conv
      (fun function_parameter =>
        let '{|
          contents.priority := priority;
            contents.seed_nonce_hash := seed_nonce_hash;
            contents.proof_of_work_nonce := proof_of_work_nonce
            |} := function_parameter in
        (priority, proof_of_work_nonce, seed_nonce_hash))
      (fun function_parameter =>
        let '(priority, proof_of_work_nonce, seed_nonce_hash) :=
          function_parameter in
        {| contents.priority := priority;
          contents.seed_nonce_hash := seed_nonce_hash;
          contents.proof_of_work_nonce := proof_of_work_nonce |}) None
      (Data_encoding.obj3
        (Data_encoding.req None None "priority" Data_encoding.uint16)
        (Data_encoding.req None None "proof_of_work_nonce"
          (Data_encoding.Fixed.__bytes_value
            Constants_repr.proof_of_work_nonce_size))
        (Data_encoding.opt None None "seed_nonce_hash" Nonce_hash.encoding))).

Definition protocol_data_encoding : Data_encoding.encoding protocol_data :=
  (let arg := Data_encoding.def "block_header.alpha.signed_contents" in
  fun eta => arg None None eta)
    (Data_encoding.conv
      (fun function_parameter =>
        let '{|
          protocol_data.contents := contents;
            protocol_data.signature := signature
            |} := function_parameter in
        (contents, signature))
      (fun function_parameter =>
        let '(contents, signature) := function_parameter in
        {| protocol_data.contents := contents;
          protocol_data.signature := signature |}) None
      (Data_encoding.merge_objs contents_encoding
        (Data_encoding.obj1
          (Data_encoding.req None None "signature" Signature.encoding)))).

Definition __raw_value (function_parameter : block_header) : Block_header.t :=
  let '{|
    block_header.shell := shell;
      block_header.protocol_data := protocol_data
      |} := function_parameter in
  let protocol_data :=
    Data_encoding.Binary.to_bytes_exn protocol_data_encoding protocol_data in
  {| Block_header.t.shell := shell;
    Block_header.t.protocol_data := protocol_data |}.

Definition unsigned_encoding
  : Data_encoding.encoding (Block_header.shell_header * contents) :=
  Data_encoding.merge_objs Block_header.shell_header_encoding contents_encoding.

Definition encoding : Data_encoding.encoding block_header :=
  (let arg := Data_encoding.def "block_header.alpha.full_header" in
  fun eta => arg None None eta)
    (Data_encoding.conv
      (fun function_parameter =>
        let '{|
          block_header.shell := shell;
            block_header.protocol_data := protocol_data
            |} := function_parameter in
        (shell, protocol_data))
      (fun function_parameter =>
        let '(shell, protocol_data) := function_parameter in
        {| block_header.shell := shell;
          block_header.protocol_data := protocol_data |}) None
      (Data_encoding.merge_objs Block_header.shell_header_encoding
        protocol_data_encoding)).

Definition max_header_length : int :=
  let fake_shell :=
    {|
      Block_header.shell_header.level :=
        (* ❌ Constant of type int32 is converted to int *)
        0; Block_header.shell_header.proto_level := 0;
      Block_header.shell_header.predecessor := (|Block_hash|).(S.HASH.zero);
      Block_header.shell_header.timestamp :=
        Time.of_seconds
          (* ❌ Constant of type int64 is converted to int *)
          0; Block_header.shell_header.validation_passes := 0;
      Block_header.shell_header.operations_hash :=
        (|Operation_list_list_hash|).(S.MERKLE_TREE.zero);
      Block_header.shell_header.fitness :=
        Fitness_repr.from_int64
          (* ❌ Constant of type int64 is converted to int *)
          0; Block_header.shell_header.context := (|Context_hash|).(S.HASH.zero)
      |} in
  let fake_contents :=
    {| contents.priority := 0; contents.seed_nonce_hash := Some Nonce_hash.zero;
      contents.proof_of_work_nonce :=
        MBytes.create Constants_repr.proof_of_work_nonce_size |} in
  Data_encoding.Binary.length encoding
    {| block_header.shell := fake_shell;
      block_header.protocol_data :=
        {| protocol_data.contents := fake_contents;
          protocol_data.signature := Signature.zero |} |}.

Definition hash_raw : Block_header.t -> (|Block_hash|).(S.HASH.t) :=
  Block_header.__hash_value.

Definition __hash_value (function_parameter : block_header)
  : (|Block_hash|).(S.HASH.t) :=
  let '{|
    block_header.shell := shell;
      block_header.protocol_data := protocol_data
      |} := function_parameter in
  Block_header.__hash_value
    {| Block_header.t.shell := shell;
      Block_header.t.protocol_data :=
        Data_encoding.Binary.to_bytes_exn protocol_data_encoding protocol_data
      |}.
