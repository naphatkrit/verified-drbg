Require Import Integers.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import DRBG_working_state.

Definition state_handle: Type := (DRBG_working_state)%type.

Inductive result :=
| error: result
| catastrophic_error: result
| success: state_handle -> result.

Inductive entropy_result :=
| entropy_error: entropy_result
| entropy_success: list Z -> entropy_result.

Definition DRBG_instantiate_function (get_entropy_input: Z -> Z -> Z -> bool -> entropy_result) (min_entropy_length max_entropy_length: Z) (get_nonce: unit -> list Z) (instantiate_algorithm: list Z -> list Z -> list Z -> Z -> DRBG_working_state) (highest_supported_security_strength: Z) (max_personalization_string_length: Z) (prediction_resistance_supported: bool) (requested_instantiation_security_strength: Z) (prediction_resistance_flag: bool) (personalization_string: list Z): result :=
  if Z.gtb requested_instantiation_security_strength highest_supported_security_strength then error
  else match prediction_resistance_flag, prediction_resistance_supported with
         | true, false => error
         | _,_ =>
           if Z.gtb (Z.of_nat (length personalization_string)) max_personalization_string_length then error
           else
             let security_strength := requested_instantiation_security_strength in (* TODO actually follow specs *)
             match get_entropy_input security_strength min_entropy_length max_entropy_length prediction_resistance_flag with
               | entropy_error => catastrophic_error
               | entropy_success entropy_input =>
                 let nonce := get_nonce tt in
                 let initial_working_state := instantiate_algorithm entropy_input nonce personalization_string security_strength in
                 success initial_working_state (* TODO store other info like prediction_resistance *)
             end
       end.
             