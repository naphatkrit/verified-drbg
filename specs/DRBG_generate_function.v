Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import DRBG_state_handle.
Require Import DRBG_generate_algorithm_result.

Inductive generate_result :=
| generate_error: generate_result
| generate_success: list Z -> DRBG_state_handle -> generate_result.

Fixpoint DRBG_generate_function_helper (generate_algorithm: DRBG_working_state -> Z -> list Z -> DRBG_generate_algorithm_result) (working_state: DRBG_working_state) (requested_number_of_bytes: Z) (additional_input: list Z) (should_reseed: bool) (count: nat): (list Z * DRBG_working_state) :=
  if should_reseed then ([], ([], [], 0)) (* TODO reseed *)
  else
    match count with
      | O => ([], ([], [], 0)) (* TODO reseed *)
      | S count' =>
        match generate_algorithm working_state requested_number_of_bytes additional_input with
          | generate_algorithm_reseed_required => DRBG_generate_function_helper generate_algorithm working_state requested_number_of_bytes additional_input true count'
          | generate_algorithm_success x y => (x, y)
        end
    end.

Definition DRBG_generate_function (generate_algorithm: DRBG_working_state -> Z -> list Z -> DRBG_generate_algorithm_result) (max_number_of_bytes_per_request: Z) (max_additional_input_length: Z) (state_handle: DRBG_state_handle) (requested_number_of_bytes requested_security_strength: Z) (prediction_resistance_request: bool) (additional_input: list Z) :=
  let '(working_state, security_strength, prediction_resistance_flag) := state_handle in
  if Z.gtb requested_number_of_bytes max_number_of_bytes_per_request then generate_error
  else
    if Z.gtb requested_security_strength security_strength then generate_error
    else
      if Z.gtb (Z.of_nat (length additional_input)) max_additional_input_length then generate_error
      else
        if prediction_resistance_request && (negb prediction_resistance_flag) then generate_error
        else
          let (output, new_working_state) := DRBG_generate_function_helper generate_algorithm working_state requested_number_of_bytes additional_input prediction_resistance_request 1%nat in
          generate_success output (new_working_state, security_strength, prediction_resistance_flag).
              
              
                                                                                             
