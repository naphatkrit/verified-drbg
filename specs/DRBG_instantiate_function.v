Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import DRBG_state_handle.
Require Import entropy.

Inductive instantiate_result :=
| instantiate_error: stream -> instantiate_result
| instantiate_catastrophic_error: stream -> instantiate_result
| instantiate_success: DRBG_state_handle -> stream -> instantiate_result.

Definition DRBG_instantiate_function (instantiate_algorithm: list Z -> list Z -> list Z -> Z -> DRBG_working_state) (min_entropy_length max_entropy_length: Z) (get_nonce: unit -> list Z) (highest_supported_security_strength: Z) (max_personalization_string_length: Z) (prediction_resistance_supported: bool) (entropy_stream: stream) (requested_instantiation_security_strength: Z) (prediction_resistance_flag: bool) (personalization_string: list Z): instantiate_result :=
  if Z.gtb requested_instantiation_security_strength highest_supported_security_strength then instantiate_error entropy_stream
  else match prediction_resistance_flag, prediction_resistance_supported with
         | true, false => instantiate_error entropy_stream
         | _,_ =>
           if Z.gtb (Z.of_nat (length personalization_string)) max_personalization_string_length then instantiate_error entropy_stream
           else
             let security_strength := requested_instantiation_security_strength in (* TODO actually follow specs *)
             match get_entropy security_strength min_entropy_length max_entropy_length prediction_resistance_flag entropy_stream with
               | entropy_error => instantiate_catastrophic_error entropy_stream
               | entropy_success (entropy_input, entropy_stream) =>
                 let nonce := get_nonce tt in
                 let initial_working_state := instantiate_algorithm entropy_input nonce personalization_string security_strength in
                 instantiate_success (initial_working_state, security_strength, prediction_resistance_flag) entropy_stream
             end
       end.
