Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.
Require Import DRBG_state_handle.
Require Import DRBG_generate_algorithm_result.
Require Import DRBG_reseed_function.

Inductive generate_result :=
| generate_error: generate_result
| generate_success: list Z -> DRBG_state_handle -> generate_result.

Fixpoint DRBG_generate_function_helper (generate_algorithm: DRBG_working_state -> Z -> list Z -> DRBG_generate_algorithm_result) (reseed_function: DRBG_state_handle -> bool -> list Z -> reseed_result) (state_handle: DRBG_state_handle) (requested_number_of_bytes: Z) (prediction_resistance_request: bool) (additional_input: list Z) (should_reseed: bool) (count: nat): (list Z * DRBG_working_state) :=
  let (state_handle, additional_input) := if should_reseed then
                        match reseed_function state_handle prediction_resistance_request additional_input with
                          | reseed_success x => (x, [])
                          | _ => (state_handle, []) (* TODO bogus *)
                        end
                      else (state_handle, additional_input) in
  let '(working_state, security_strength, prediction_resistance_flag) := state_handle in
  match generate_algorithm working_state requested_number_of_bytes additional_input with
    | generate_algorithm_reseed_required =>
      match count with
        | O => ([], ([], [], 0)) (* impossible *)
        | S count' => DRBG_generate_function_helper generate_algorithm reseed_function state_handle requested_number_of_bytes prediction_resistance_request additional_input true count'
      end
    | generate_algorithm_success x y => (x, y)
  end.

Definition DRBG_generate_function (generate_algorithm: DRBG_working_state -> Z -> list Z -> DRBG_generate_algorithm_result) (reseed_function: DRBG_state_handle -> bool -> list Z -> reseed_result) (max_number_of_bytes_per_request: Z) (max_additional_input_length: Z) (state_handle: DRBG_state_handle) (requested_number_of_bytes requested_security_strength: Z) (prediction_resistance_request: bool) (additional_input: list Z) :=
  let '(working_state, security_strength, prediction_resistance_flag) := state_handle in
  if Z.gtb requested_number_of_bytes max_number_of_bytes_per_request then generate_error
  else
    if Z.gtb requested_security_strength security_strength then generate_error
    else
      if Z.gtb (Z.of_nat (length additional_input)) max_additional_input_length then generate_error
      else
        if prediction_resistance_request && (negb prediction_resistance_flag) then generate_error
        else
          let (output, new_working_state) := DRBG_generate_function_helper generate_algorithm reseed_function state_handle requested_number_of_bytes prediction_resistance_request additional_input prediction_resistance_request 1%nat in
          generate_success output (new_working_state, security_strength, prediction_resistance_flag).
