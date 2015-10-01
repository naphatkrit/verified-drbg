Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_state_handle.
Require Import DRBG_working_state.
Require Import DRBG_entropy_result.

Inductive reseed_result :=
| reseed_error: reseed_result
| reseed_catastrophic_error: reseed_result
| reseed_success: DRBG_state_handle -> reseed_result.

Definition DRBG_reseed_function (reseed_algorithm: DRBG_working_state -> list Z -> list Z -> DRBG_working_state) (get_entropy_input: Z -> Z -> Z -> bool -> entropy_result) (min_entropy_length max_entropy_length: Z) (max_additional_input_length: Z) (state_handle: DRBG_state_handle) (prediction_resistance_request: bool) (additional_input: list Z): reseed_result :=
  let '(working_state, security_strength, prediction_resistance_flag) := state_handle in
  if prediction_resistance_request && (negb prediction_resistance_flag) then reseed_error
  else
    match prediction_resistance_flag, prediction_resistance_flag with
      | true, false => reseed_error
      | _,_ =>
        if Z.gtb (Z.of_nat (length additional_input)) max_additional_input_length then reseed_error
        else
          match get_entropy_input security_strength min_entropy_length max_entropy_length prediction_resistance_flag with
            | entropy_error => reseed_catastrophic_error
            | entropy_success entropy_input =>
              let new_working_state := reseed_algorithm working_state entropy_input additional_input in
              reseed_success (new_working_state, security_strength, prediction_resistance_flag)
          end
    end.

           
