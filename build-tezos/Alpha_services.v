(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Set Primitive Projections.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Require Import Tezos.Environment.
Import Environment.Notations.
Require Tezos.Alpha_context.
Require Tezos.Constants_services_mli. Module Constants_services := Constants_services_mli.
Require Tezos.Contract_services_mli. Module Contract_services := Contract_services_mli.
Require Tezos.Delegate_services_mli. Module Delegate_services := Delegate_services_mli.
Require Tezos.Helpers_services_mli. Module Helpers_services := Helpers_services_mli.
Require Tezos.Nonce_hash.
Require Tezos.Seed_repr.
Require Tezos.Services_registration.
Require Tezos.Storage_mli. Module Storage := Storage_mli.
Require Tezos.Voting_services_mli. Module Voting_services := Voting_services_mli.

Import Alpha_context.

Definition custom_root {A : Set} : RPC_path.context A := RPC_path.open_root.

Module Seed.
  Module S.
    Import Data_encoding.
    
    Definition __seed_value
      : RPC_service.service Updater.rpc_context Updater.rpc_context unit unit
        Alpha_context.Seed.seed :=
      RPC_service.post_service
        (Some "Seed of the cycle to which the block belongs.") RPC_query.empty
        Data_encoding.empty Alpha_context.Seed.seed_encoding
        (RPC_path.op_div (RPC_path.op_div custom_root "context") "seed").
  End S.
  
  (* ❌ Top-level evaluations are ignored *)
  (* top_level_evaluation *)
  
  Definition get {A : Set} (ctxt : RPC_context.simple A) (block : A)
    : Lwt.t (Error_monad.shell_tzresult Alpha_context.Seed.seed) :=
    RPC_context.make_call0 S.__seed_value ctxt block tt tt.
End Seed.

Module Nonce.
  Inductive info : Set :=
  | Revealed : Alpha_context.Nonce.t -> info
  | Missing : Nonce_hash.t -> info
  | Forgotten : info.
  
  Definition info_encoding : Data_encoding.encoding info :=
    Data_encoding.union None
      [
        Data_encoding.__case_value "Revealed" None (Data_encoding.Tag 0)
          (Data_encoding.obj1
            (Data_encoding.req None None "nonce"
              Alpha_context.Nonce.encoding))
          (fun function_parameter =>
            match function_parameter with
            | Revealed __nonce_value => Some __nonce_value
            | _ => None
            end) (fun __nonce_value => Revealed __nonce_value);
        Data_encoding.__case_value "Missing" None (Data_encoding.Tag 1)
          (Data_encoding.obj1
            (Data_encoding.req None None "hash" Nonce_hash.encoding))
          (fun function_parameter =>
            match function_parameter with
            | Missing __nonce_value => Some __nonce_value
            | _ => None
            end) (fun __nonce_value => Missing __nonce_value);
        Data_encoding.__case_value "Forgotten" None (Data_encoding.Tag 2)
          Data_encoding.empty
          (fun function_parameter =>
            match function_parameter with
            | Forgotten => Some tt
            | _ => None
            end)
          (fun function_parameter =>
            let '_ := function_parameter in
            Forgotten)
      ].
  
  Module S.
    Definition get
      : RPC_service.service Updater.rpc_context
        (Updater.rpc_context * Alpha_context.Raw_level.raw_level) unit unit info :=
      RPC_service.get_service (Some "Info about the nonce of a previous block.")
        RPC_query.empty info_encoding
        (RPC_path.op_divcolon
          (RPC_path.op_div (RPC_path.op_div custom_root "context") "nonces")
          Alpha_context.Raw_level.rpc_arg).
  End S.
  
  Definition register (function_parameter : unit) : unit :=
    let '_ := function_parameter in
    Services_registration.register1 S.get
      (fun ctxt =>
        fun raw_level =>
          fun function_parameter =>
            let '_ := function_parameter in
            fun function_parameter =>
              let '_ := function_parameter in
              let level := Alpha_context.Level.from_raw ctxt None raw_level in
              let= function_parameter := Alpha_context.Nonce.get ctxt level in
              match function_parameter with
              | Pervasives.Ok (Storage.Revealed __nonce_value) =>
                Error_monad.__return (Revealed __nonce_value)
              |
                Pervasives.Ok
                  (Storage.Unrevealed {|
                    Storage.unrevealed_nonce.nonce_hash := nonce_hash |}) =>
                Error_monad.__return (Missing nonce_hash)
              | Pervasives.Error _ => Error_monad.__return Forgotten
              end).
  
  Definition get {A : Set}
    (ctxt : RPC_context.simple A) (block : A)
    (level : Alpha_context.Raw_level.raw_level)
    : Lwt.t (Error_monad.shell_tzresult info) :=
    RPC_context.make_call1 S.get ctxt block level tt tt.
End Nonce.

Module Contract := Contract_services.

Module Constants := Constants_services.

Module Delegate := Delegate_services.

Module Helpers := Helpers_services.

Module Forge := Helpers_services.Forge.

Module Parse := Helpers_services.Parse.

Module Voting := Voting_services.

Definition register (function_parameter : unit) : unit :=
  let '_ := function_parameter in
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  (* ❌ Sequences of instructions are ignored (operator ";") *)
  (* ❌ instruction_sequence ";" *)
  Voting.register tt.
