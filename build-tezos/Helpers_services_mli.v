(** Generated by coq-of-ocaml *)
Require Import OCaml.OCaml.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.
Import ListNotations.

Unset Positivity Checking.
Unset Guard Checking.

Require Import Tezos.Environment.
Require Tezos.Alpha_context.
Require Tezos.Apply_results.
Require Tezos.Michelson_v1_primitives.
Require Tezos.Nonce_hash.
Require Tezos.Script_interpreter.
Require Tezos.Script_tc_errors.

Import Alpha_context.

(* extensible_type error *)

Parameter current_level : forall {E F H J K a b c i o q : Set},
  (((RPC_service.t
    ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit +
      (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
  Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t (RPC_context.t * a) q i o -> a ->
    a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o))
      *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (J * a * b * c * q * i * o)) * K))))
    * K * a -> option int32 -> a ->
  Lwt.t (Error_monad.shell_tzresult Alpha_context.Level.t).

Parameter levels_in_current_cycle : forall {E F H J K a b c i o q : Set},
  (((RPC_service.t
    ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit +
      (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
  Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t (RPC_context.t * a) q i o -> a ->
    a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o))
      *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (J * a * b * c * q * i * o)) * K))))
    * K * a -> option int32 -> a ->
  Lwt.t
    (Error_monad.shell_tzresult
      (Alpha_context.Raw_level.t * Alpha_context.Raw_level.t)).

Module Scripts.
  Parameter run_code : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr ->
    Alpha_context.Script.expr * Alpha_context.Script.expr * Alpha_context.Tez.t
      * (|Chain_id|).(S.HASH.t) * option Alpha_context.Contract.t *
      option Alpha_context.Contract.t * option Z.t * string ->
    Lwt.t
      (Error_monad.shell_tzresult
        (Alpha_context.Script.expr *
          list Alpha_context.packed_internal_operation *
          option Alpha_context.Contract.big_map_diff)).
  
  Parameter trace_code : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr ->
    Alpha_context.Script.expr * Alpha_context.Script.expr * Alpha_context.Tez.t
      * (|Chain_id|).(S.HASH.t) * option Alpha_context.Contract.t *
      option Alpha_context.Contract.t * option Z.t * string ->
    Lwt.t
      (Error_monad.shell_tzresult
        (Alpha_context.Script.expr *
          list Alpha_context.packed_internal_operation *
          Script_interpreter.execution_trace *
          option Alpha_context.Contract.big_map_diff)).
  
  Parameter typecheck_code : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr * option Z.t ->
    Lwt.t
      (Error_monad.shell_tzresult
        (Script_tc_errors.type_map * Alpha_context.Gas.t)).
  
  Parameter typecheck_data : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr * Alpha_context.Script.expr * option Z.t ->
    Lwt.t (Error_monad.shell_tzresult Alpha_context.Gas.t).
  
  Parameter pack_data : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr * Alpha_context.Script.expr * option Z.t ->
    Lwt.t (Error_monad.shell_tzresult (MBytes.t * Alpha_context.Gas.t)).
  
  Parameter run_operation : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.packed_operation * (|Chain_id|).(S.HASH.t) ->
    Lwt.t
      (Error_monad.shell_tzresult
        (Alpha_context.packed_protocol_data *
          Apply_results.packed_operation_metadata)).
  
  Parameter entrypoint_type : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr * string ->
    Lwt.t (Error_monad.shell_tzresult Alpha_context.Script.expr).
  
  Parameter list_entrypoints : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Script.expr ->
    Lwt.t
      (Error_monad.shell_tzresult
        (list (list Michelson_v1_primitives.prim) *
          list (string * Alpha_context.Script.expr))).
End Scripts.

Module Forge.
  Module Manager.
    Parameter operations : forall {E F H J K a b c i o q : Set},
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t RPC_context.t q i
        o -> a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) *
        (E * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (RPC_context.t * a) q i o -> a -> a -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
          Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
            (((RPC_service.t
              ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
                (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
              (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
            i -> Lwt.t (Error_monad.shell_tzresult o)) *
              (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
      (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
      option Alpha_context.public_key -> Alpha_context.counter ->
      Alpha_context.Tez.t -> Z.t -> Z.t ->
      list Alpha_context.packed_manager_operation ->
      Lwt.t (Error_monad.shell_tzresult MBytes.t).
    
    Parameter reveal : forall {E F H J K a b c i o q : Set},
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t RPC_context.t q i
        o -> a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) *
        (E * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (RPC_context.t * a) q i o -> a -> a -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
          Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
            (((RPC_service.t
              ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
                (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
              (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
            i -> Lwt.t (Error_monad.shell_tzresult o)) *
              (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
      (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
      Alpha_context.public_key -> Alpha_context.counter ->
      Alpha_context.Tez.t -> unit -> Lwt.t (Error_monad.shell_tzresult MBytes.t).
    
    Parameter transaction : forall {E F H J K a b c i o q : Set},
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t RPC_context.t q i
        o -> a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) *
        (E * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (RPC_context.t * a) q i o -> a -> a -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
          Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
            (((RPC_service.t
              ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
                (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
              (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
            i -> Lwt.t (Error_monad.shell_tzresult o)) *
              (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
      (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
      option Alpha_context.public_key -> Alpha_context.counter ->
      Alpha_context.Tez.t -> Alpha_context.Contract.t -> option string ->
      option Alpha_context.Script.expr -> Z.t -> Z.t -> Alpha_context.Tez.t ->
      unit -> Lwt.t (Error_monad.shell_tzresult MBytes.t).
    
    Parameter origination : forall {E F H J K a b c i o q : Set},
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t RPC_context.t q i
        o -> a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) *
        (E * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (RPC_context.t * a) q i o -> a -> a -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
          Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
            (((RPC_service.t
              ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
                (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
              (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
            i -> Lwt.t (Error_monad.shell_tzresult o)) *
              (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
      (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
      option Alpha_context.public_key -> Alpha_context.counter ->
      Alpha_context.Tez.t -> option Alpha_context.public_key_hash ->
      Alpha_context.Script.t -> Z.t -> Z.t -> Alpha_context.Tez.t -> unit ->
      Lwt.t (Error_monad.shell_tzresult MBytes.t).
    
    Parameter delegation : forall {E F H J K a b c i o q : Set},
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t RPC_context.t q i
        o -> a -> q -> i -> Lwt.t (Error_monad.shell_tzresult o)) *
        (E * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          (RPC_context.t * a) q i o -> a -> a -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
          Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
            (((RPC_service.t
              ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
                (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
              (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
            i -> Lwt.t (Error_monad.shell_tzresult o)) *
              (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
      (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
      option Alpha_context.public_key -> Alpha_context.counter ->
      Alpha_context.Tez.t -> option Alpha_context.public_key_hash ->
      Lwt.t (Error_monad.shell_tzresult MBytes.t).
  End Manager.
  
  Parameter endorsement : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) -> Alpha_context.Raw_level.t -> unit ->
    Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter proposals : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
    Alpha_context.Voting_period.t -> list (|Protocol_hash|).(S.HASH.t) ->
    unit -> Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter ballot : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) -> Alpha_context.public_key_hash ->
    Alpha_context.Voting_period.t -> (|Protocol_hash|).(S.HASH.t) ->
    Alpha_context.Vote.ballot -> unit ->
    Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter seed_nonce_revelation : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) -> Alpha_context.Raw_level.t ->
    Alpha_context.Nonce.t -> unit -> Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter double_baking_evidence : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) -> Alpha_context.Block_header.t ->
    Alpha_context.Block_header.t -> unit ->
    Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter double_endorsement_evidence : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    (|Block_hash|).(S.HASH.t) ->
    Alpha_context.operation Alpha_context.Kind.endorsement ->
    Alpha_context.operation Alpha_context.Kind.endorsement -> unit ->
    Lwt.t (Error_monad.shell_tzresult MBytes.t).
  
  Parameter protocol_data : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a -> Z ->
    option Nonce_hash.t -> option MBytes.t -> unit ->
    Lwt.t (Error_monad.shell_tzresult MBytes.t).
End Forge.

Module Parse.
  Parameter operations : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a -> option bool ->
    list Alpha_context.Operation.raw ->
    Lwt.t (Error_monad.shell_tzresult (list Alpha_context.Operation.packed)).
  
  Parameter block : forall {E F H J K a b c i o q : Set},
    (((RPC_service.t
      ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit + (* `POST *) unit
        + (* `PATCH *) unit) RPC_context.t RPC_context.t q i o -> a -> q -> i ->
    Lwt.t (Error_monad.shell_tzresult o)) * (E * q * i * o)) *
      (((RPC_service.t
        ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
          (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
        (RPC_context.t * a) q i o -> a -> a -> q -> i ->
      Lwt.t (Error_monad.shell_tzresult o)) * (F * a * q * i * o)) *
        (((RPC_service.t
          ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
            (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
          ((RPC_context.t * a) * b) q i o -> a -> a -> b -> q -> i ->
        Lwt.t (Error_monad.shell_tzresult o)) * (H * a * b * q * i * o)) *
          (((RPC_service.t
            ((* `PUT *) unit + (* `GET *) unit + (* `DELETE *) unit +
              (* `POST *) unit + (* `PATCH *) unit) RPC_context.t
            (((RPC_context.t * a) * b) * c) q i o -> a -> a -> b -> c -> q ->
          i -> Lwt.t (Error_monad.shell_tzresult o)) *
            (J * a * b * c * q * i * o)) * K)))) * K * a -> a ->
    Alpha_context.Block_header.shell_header -> MBytes.t ->
    Lwt.t (Error_monad.shell_tzresult Alpha_context.Block_header.protocol_data).
End Parse.

Parameter register : unit -> unit.